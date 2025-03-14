/*-------------------------------------------------------------------------
 *
 * verify_brinam.c
 *	  Functions to check postgresql brin indexes for corruption
 *
 * Copyright (c) 2016-2024, PostgreSQL Global Development Group
 *
 *	  contrib/amcheck/verify_brinam.c
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/heaptoast.h"
#include "access/htup_details.h"
#include "access/nbtree.h"
#include "access/table.h"
#include "access/tableam.h"
#include "access/transam.h"
#include "access/xact.h"
#include "catalog/index.h"
#include "catalog/pg_am.h"
#include "catalog/pg_opfamily_d.h"
#include "commands/tablecmds.h"
#include "common/pg_prng.h"
#include "lib/bloomfilter.h"
#include "miscadmin.h"
#include "storage/lmgr.h"
#include "storage/smgr.h"
#include "utils/guc.h"
#include "utils/memutils.h"
#include "utils/snapmgr.h"
#include "access/brin_page.h"
#include "access/brin_revmap.h"
#include "catalog/pg_operator.h"
#include "utils/lsyscache.h"

PG_FUNCTION_INFO_V1(brin_index_check);

typedef struct BrinCheckState {
    Relation idxrel;
    Relation heaprel;
    BufferAccessStrategy checkstrategy;
    BrinRevmap *revmap;
    BrinDesc *bdesc;
    int natts;
    Buffer buf;
    FmgrInfo *consistentFn;
    BlockNumber pagesPerRange;
    ScanKey *scanKeys;
    double rangeCount;
    BlockNumber nextRangeStartBlockNumber;
    BrinMemTuple *dtup;
    bool dtupvalid;
    bool *rangeAllNulls;
    MemoryContext brinRangeCtx;
    MemoryContext heapTupleCtx;
    double invalidCount;
} BrinCheckState;

static void brin_index_check_internal(Oid indrelid);

static inline void brin_index_checkable(Relation rel);

static inline bool brin_index_mainfork_expected(Relation rel);

static void brin_check(Relation idxrel, Relation heaprel);

bool index_tuple_was_moved_to_another_page(Buffer revmapbuf, uint32 revmapIdx, BlockNumber oldbn);

static void
brin_check_callback(Relation index,
                    ItemPointer tid,
                    Datum *values,
                    bool *isnull,
                    bool tupleIsAlive,
                    void *brstate);

static void check_heap_tuple(BrinCheckState *state, const Datum *values, const bool *nulls);

ScanKey prepare_scan_key(const BrinCheckState *state, AttrNumber attno);

void check_brin_index_structure(BrinCheckState *pState);

void check_all_heap_consistent(Relation idxrel, Relation heaprel, BrinCheckState *state);

static ItemId
PageGetItemIdCareful(BrinCheckState *state, BlockNumber block, Page page,
                     OffsetNumber offset);

Datum
brin_index_check(PG_FUNCTION_ARGS) {
    Oid indrelid = PG_GETARG_OID(0);

    brin_index_check_internal(indrelid);

    PG_RETURN_VOID();
}

/*
 * Helper for bt_index_[parent_]check, coordinating the bulk of the work.
 */
static void
brin_index_check_internal(Oid indrelid) {
    Oid heapid;
    Relation indrel;
    Relation heaprel;
    LOCKMODE lockmode = ShareUpdateExclusiveLock;
    Oid save_userid;
    int save_sec_context;
    int save_nestlevel;


    /*
     * We must lock table before index to avoid deadlocks.  However, if the
     * passed indrelid isn't an index then IndexGetRelation() will fail.
     * Rather than emitting a not-very-helpful error message, postpone
     * complaining, expecting that the is-it-an-index test below will fail.
     *
     * In hot standby mode this will raise an error when parentcheck is true.
     */
    heapid = IndexGetRelation(indrelid, true);
    if (OidIsValid(heapid)) {
        heaprel = table_open(heapid, lockmode);

        /*
         * Switch to the table owner's userid, so that any index functions are
         * run as that user.  Also lock down security-restricted operations
         * and arrange to make GUC variable changes local to this command.
         */
        GetUserIdAndSecContext(&save_userid, &save_sec_context);
        SetUserIdAndSecContext(heaprel->rd_rel->relowner,
                               save_sec_context | SECURITY_RESTRICTED_OPERATION);
        save_nestlevel = NewGUCNestLevel();
        RestrictSearchPath();
    } else {
        heaprel = NULL;
        /* Set these just to suppress "uninitialized variable" warnings */
        save_userid = InvalidOid;
        save_sec_context = -1;
        save_nestlevel = -1;
    }

    /*
     * Open the target index relations separately (like relation_openrv(), but
     * with heap relation locked first to prevent deadlocking).  In hot
     * standby mode this will raise an error when parentcheck is true.
     *
     * There is no need for the usual indcheckxmin usability horizon test
     * here, even in the heapallindexed case, because index undergoing
     * verification only needs to have entries for a new transaction snapshot.
     * (If this is a parentcheck verification, there is no question about
     * committed or recently dead heap tuples lacking index entries due to
     * concurrent activity.)
     */
    indrel = index_open(indrelid, lockmode);

    /*
     * Since we did the IndexGetRelation call above without any lock, it's
     * barely possible that a race against an index drop/recreation could have
     * netted us the wrong table.
     */
    if (heaprel == NULL || heapid != IndexGetRelation(indrelid, false))
        ereport(ERROR,
                (errcode(ERRCODE_UNDEFINED_TABLE),
                        errmsg("could not open parent table of index \"%s\"",
                               RelationGetRelationName(indrel))));

    /* Relation suitable for checking as BRIN? */
    brin_index_checkable(indrel);

    if (brin_index_mainfork_expected(indrel)) {
        /* Check index, possibly against table it is an index on */
        brin_check(indrel, heaprel);
    }

    /* Roll back any GUC changes executed by index functions */
    AtEOXact_GUC(false, save_nestlevel);

    /* Restore userid and security context */
    SetUserIdAndSecContext(save_userid, save_sec_context);

    /*
     * Release locks early. That's ok here because nothing in the called
     * routines will trigger shared cache invalidations to be sent, so we can
     * relax the usual pattern of only releasing locks after commit.
     */
    index_close(indrel, lockmode);
    if (heaprel)
        table_close(heaprel, lockmode);
}

/*
 * Basic checks about the suitability of a relation for checking as a B-Tree
 * index.
 *
 * NB: Intentionally not checking permissions, the function is normally not
 * callable by non-superusers. If granted, it's useful to be able to check a
 * whole cluster.
 */
static inline void
brin_index_checkable(Relation rel) {
    if (rel->rd_rel->relkind != RELKIND_INDEX ||
        rel->rd_rel->relam != BRIN_AM_OID)
        ereport(ERROR,
                (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                        errmsg("only BRIN indexes are supported as targets for verification"),
                        errdetail("Relation \"%s\" is not a BRIN index.",
                                  RelationGetRelationName(rel))));

    if (RELATION_IS_OTHER_TEMP(rel))
        ereport(ERROR,
                (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                        errmsg("cannot access temporary tables of other sessions"),
                        errdetail("Index \"%s\" is associated with temporary relation.",
                                  RelationGetRelationName(rel))));

    if (!rel->rd_index->indisvalid)
        ereport(ERROR,
                (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                        errmsg("cannot check index \"%s\"",
                               RelationGetRelationName(rel)),
                        errdetail("Index is not valid.")));
}

/*
 * Check if B-Tree index relation should have a file for its main relation
 * fork.  Verification uses this to skip unlogged indexes when in hot standby
 * mode, where there is simply nothing to verify.  We behave as if the
 * relation is empty.
 *
 * NB: Caller should call brin_index_checkable() before calling here.
 */
static inline bool
brin_index_mainfork_expected(Relation rel) {
    if (rel->rd_rel->relpersistence != RELPERSISTENCE_UNLOGGED ||
        !RecoveryInProgress())
        return true;

    ereport(DEBUG1,
            (errcode(ERRCODE_READ_ONLY_SQL_TRANSACTION),
                    errmsg("cannot verify unlogged index \"%s\" during recovery, skipping",
                           RelationGetRelationName(rel))));

    return false;
}

void brin_check(Relation idxrel, Relation heaprel) {
    BrinCheckState *state;

    /*
	 * Initialize state for entire verification operation
	 */
    state = palloc0(sizeof(BrinCheckState));
    state->idxrel = idxrel;
    state->heaprel = heaprel;
    state->checkstrategy = GetAccessStrategy(BAS_BULKREAD);
    state->bdesc = brin_build_desc(idxrel);
    state->revmap = brinRevmapInitialize(idxrel, &state->pagesPerRange);
    state->natts = state->bdesc->bd_tupdesc->natts;
    state->dtup = brin_new_memtuple(state->bdesc);
    state->dtupvalid = false;
    state->consistentFn = palloc0_array(FmgrInfo, state->natts);
    state->rangeAllNulls = palloc0_array(bool, state->natts);
    state->rangeCount = 0;
    state->invalidCount = 0;
    state->nextRangeStartBlockNumber = 0; // next range is the first range in the beginning
    state->scanKeys = palloc0_array(ScanKey, state->natts);
    state->brinRangeCtx = AllocSetContextCreate(CurrentMemoryContext,
                                                "brin check range context",
                                                ALLOCSET_DEFAULT_SIZES);
    state->heapTupleCtx = AllocSetContextCreate(CurrentMemoryContext,
                                                "brin check tuple context",
                                                ALLOCSET_DEFAULT_SIZES);

    check_brin_index_structure(state);
    check_all_heap_consistent(idxrel, heaprel, state);


    if (state->buf != InvalidBuffer)
        ReleaseBuffer(state->buf);

    brin_free_desc(state->bdesc);
    brinRevmapTerminate(state->revmap);
    MemoryContextDelete(state->brinRangeCtx);
    MemoryContextDelete(state->heapTupleCtx);
}

/*
 * We hold ShareUpdateExclusiveLock, so revmap could not be extended while check as well as
 * all regular pages should stay regular and ranges could not be summarized and desummarized.
 * Nevertheless, concurrent updates could lead to new regular page allocations
 * and moving of index tuples.
 */
void check_brin_index_structure(BrinCheckState *state) {
    Buffer		metabuf;
    Page		metapage;
    BrinMetaPageData *metadata;
    Relation idxrel;
    BlockNumber revmapBlk;
    BlockNumber lastRevmapPage;
    BlockNumber idxnblocks;
    BlockNumber heapnblocks;
    BlockNumber rangeStartBlockNumber;
    BlockNumber pagesPerRange;
    Buffer		regpagebuf;
    Page		regpage;
    BrinMemTuple *dtup;


    idxrel = state->idxrel;

    /* Meta page check */
    metabuf = ReadBufferExtended(idxrel, MAIN_FORKNUM, BRIN_METAPAGE_BLKNO, RBM_NORMAL,
                                 state->checkstrategy);
    LockBuffer(metabuf, BUFFER_LOCK_SHARE);
    metapage = BufferGetPage(metabuf);
    metadata = (BrinMetaPageData *) PageGetContents(metapage);
    idxnblocks = RelationGetNumberOfBlocks(idxrel);
    heapnblocks = RelationGetNumberOfBlocks(state->heaprel);

    if (!BRIN_IS_META_PAGE(metapage) ||
        metadata->brinMagic != BRIN_META_MAGIC ||
        metadata->brinVersion != BRIN_CURRENT_VERSION ||
        metadata->pagesPerRange < 1 || metadata->pagesPerRange > 131072 || //TODO hardcode max value?
        metadata->lastRevmapPage <= BRIN_METAPAGE_BLKNO || metadata->lastRevmapPage >= idxnblocks)
    {
        ereport(ERROR,
                (errcode(ERRCODE_DATA_CORRUPTED),
                        errmsg("index is corrupted - metabuf metapage is corrupted",
                               BRIN_METAPAGE_BLKNO)));
    }

    lastRevmapPage = metadata->lastRevmapPage;
    pagesPerRange = metadata->pagesPerRange;
    LockBuffer(metabuf, BUFFER_LOCK_UNLOCK);

    /* Walk revmap and check ranges are consistent and brin tuples have expected format. */
    rangeStartBlockNumber = 0;
    regpagebuf = InvalidBuffer;
    dtup = state->dtup;
    for (revmapBlk = BRIN_METAPAGE_BLKNO + 1; revmapBlk <= lastRevmapPage; revmapBlk++) {
        Buffer		revmapbuf;
        Page		revmappage;
        uint32      revmapidx;

        revmapbuf = ReadBufferExtended(idxrel, MAIN_FORKNUM, revmapBlk, RBM_NORMAL,
                                       state->checkstrategy);
        LockBuffer(revmapbuf, BUFFER_LOCK_SHARE);
        revmappage = BufferGetPage(revmapbuf);

        /* Pages with block numbers in [1, lastRevmapPage] should be revmap pages */
        if (!BRIN_IS_REVMAP_PAGE(revmappage))
        {
            ereport(ERROR,
                    (errcode(ERRCODE_DATA_CORRUPTED),
                            errmsg("index is corrupted - expected revmap page at block %u",
                                   revmapBlk)));
        }
        LockBuffer(revmapbuf, BUFFER_LOCK_UNLOCK);

        /* Walk and check all brin tuples from current revmap page */
        revmapidx = 0;
        while (revmapidx < REVMAP_PAGE_MAXITEMS) {
            ItemPointerData *revmaptids;
            RevmapContents *contents;
            ItemPointerData *iptr;
            BlockNumber regpageBlk;
            OffsetNumber regpageoffset;
            ItemId		lp;
            BrinTuple  *tup;

            CHECK_FOR_INTERRUPTS();

            LockBuffer(revmapbuf, BUFFER_LOCK_SHARE);

            contents = (RevmapContents *) PageGetContents(BufferGetPage(revmapbuf));
            revmaptids = contents->rm_tids;
            /* Pointer for the range with start at rangeStartBlockNumber */
            iptr = revmaptids + revmapidx;

            // todo we can remember all unsummarized ranges and check there are no index tuples in regular pages for such ranges
            /* Tuple pointer is invalid means range isn't summarized, just move to the next range */
            if (!ItemPointerIsValid(iptr)) {
                elog(DEBUG1, "Range %u is not summarized", rangeStartBlockNumber);
                revmapidx++;
                rangeStartBlockNumber += pagesPerRange;
                LockBuffer(revmapbuf, BUFFER_LOCK_UNLOCK);
                continue;
            }

            /*
             * Pointer is valid and points to brin tuple for the range with start at rangeStartBlockNumber
             * Let's check it.
             */
            regpageBlk = ItemPointerGetBlockNumber(iptr);
            regpageoffset = ItemPointerGetOffsetNumber(iptr);

            LockBuffer(revmapbuf, BUFFER_LOCK_UNLOCK);

            /*
             * Check if the index tuple block number is greater than the relation size.
             * To avoid fetching the number of blocks for each tuple, use cached value first
             */
            if (regpageBlk >= idxnblocks) {

                /* Regular pages may have been added, so refresh idxnblocks and recheck */
                idxnblocks = RelationGetNumberOfBlocks(idxrel);
                if (regpageBlk >= idxnblocks) {
                    ereport(ERROR,
                            (errcode(ERRCODE_DATA_CORRUPTED),
                                    errmsg("index is corrupted - revmap item (%u, %u) must points to non existing block",
                                           regpageBlk, regpageoffset)));
                }
            }

            /*
             * To avoid some pin/unpin cycles we cache last used regular page.
             * Check if we need different regular page and fetch it.
             */
            if (!BufferIsValid(regpagebuf) || BufferGetBlockNumber(regpagebuf) != regpageBlk) {
                if (BufferIsValid(regpagebuf)) {
                    ReleaseBuffer(regpagebuf);
                }
                regpagebuf = ReadBuffer(idxrel, regpageBlk);
            }

            LockBuffer(regpagebuf, BUFFER_LOCK_SHARE);
            regpage = BufferGetPage(regpagebuf);

            /* We use ShareUpdateExclusiveLock so revmap should always point to a regular page. */
            if (!BRIN_IS_REGULAR_PAGE(regpage)) {
                ereport(ERROR,
                        (errcode(ERRCODE_DATA_CORRUPTED),
                                errmsg("index is corrupted - revmap item (%u, %u) must points to a regular page",
                                       regpageBlk, regpageoffset)));
            }

            /* Check item offset is valid */
            if (regpageoffset > PageGetMaxOffsetNumber(regpage)) {

                /* If concurrent update moved our tuple we need to retry */
                if (index_tuple_was_moved_to_another_page(revmapbuf, revmapidx, regpageBlk)) {
                    LockBuffer(regpagebuf, BUFFER_LOCK_UNLOCK);
                    continue;
                }

                ereport(ERROR,
                        (errcode(ERRCODE_DATA_CORRUPTED),
                                errmsg("index is corrupted - revmap item (%u, %u) offset number is greater than max page offset",
                                       revmapBlk, regpageoffset)));
            }

            elog(DEBUG1, "Process range: %u, iptr: (%u,%u)", rangeStartBlockNumber, regpageBlk, regpageoffset);

            lp = PageGetItemIdCareful(state, regpageBlk, regpage, regpageoffset);

            /* Revmap should point to normal tuples only */
            if (!ItemIdIsUsed(lp)) {

                /* If concurrent update moved our tuple we need to retry */
                if (index_tuple_was_moved_to_another_page(revmapbuf, revmapidx, regpageBlk)) {
                    LockBuffer(regpagebuf, BUFFER_LOCK_UNLOCK);
                    continue;
                }

                ereport(ERROR,
                        (errcode(ERRCODE_DATA_CORRUPTED),
                                errmsg("index is corrupted - revmap item (%u, %u) points to unused item",
                                       revmapBlk, regpageoffset)));

            }


            tup = (BrinTuple *) PageGetItem(regpage, lp);

            /* Check if range start block number is as expected */
            if (tup->bt_blkno != rangeStartBlockNumber) {

                /* If concurrent update moved our tuple we need to retry */
                if (index_tuple_was_moved_to_another_page(revmapbuf, revmapidx, regpageBlk)) {
                    LockBuffer(regpagebuf, BUFFER_LOCK_UNLOCK);
                    continue;
                }

                ereport(ERROR,
                        (errcode(ERRCODE_DATA_CORRUPTED),
                                errmsg("index is corrupted - index tuple (%u, %u) bt_blkno is invalid %u, expected %u",
                                       tup->bt_blkno, rangeStartBlockNumber)));
            }

            dtup = brin_deform_tuple(state->bdesc, tup, dtup);
            //todo check dtup structure

            LockBuffer(regpagebuf, BUFFER_LOCK_UNLOCK);
            rangeStartBlockNumber += pagesPerRange;
            revmapidx++;

            /*
             * For the last revmap page we must check that iptr is invalid
             * for any range with startBlockNumber >= idxnblocks
             */
            if (revmapBlk == lastRevmapPage && rangeStartBlockNumber >= heapnblocks) {
                LockBuffer(regpagebuf, BUFFER_LOCK_SHARE);
                contents = (RevmapContents *) PageGetContents(BufferGetPage(revmapbuf));
                revmaptids = contents->rm_tids;

                while (revmapidx < REVMAP_PAGE_MAXITEMS) {
                    iptr = revmaptids + revmapidx;
                    if (ItemPointerIsValid(iptr)) {
                        ereport(ERROR,
                                (errcode(ERRCODE_DATA_CORRUPTED),
                                        errmsg("index is corrupted - revmap has a valid pointer for the range with start at %u"
                                               " but table size is %u",
                                               rangeStartBlockNumber, heapnblocks)));
                    }
                    rangeStartBlockNumber += pagesPerRange;
                    revmapidx++;
                }

                LockBuffer(regpagebuf, BUFFER_LOCK_UNLOCK);
            }

        }

        elog(DEBUG1, "Complete revmap page check: %d", revmapBlk);

        if (BufferIsValid(regpagebuf))
            ReleaseBuffer(regpagebuf);

        ReleaseBuffer(revmapbuf);
    }

    /* Check all the rest pages are new or regular pages */
    idxnblocks = RelationGetNumberOfBlocks(idxrel);
    for (BlockNumber regBlk = revmapBlk; regBlk < idxnblocks; regBlk++) {
        regpagebuf = ReadBufferExtended(idxrel, MAIN_FORKNUM, revmapBlk, RBM_NORMAL,
                           state->checkstrategy);
        LockBuffer(regpagebuf, BUFFER_LOCK_SHARE);
        regpage = BufferGetPage(regpagebuf);

        if (!PageIsNew(regpage) && !BRIN_IS_REGULAR_PAGE(regpage))
        {
            ereport(ERROR,
                    (errcode(ERRCODE_DATA_CORRUPTED),
                            errmsg("index is corrupted - expected new or regular page at block %u",
                                   revmapBlk)));
        }

        UnlockReleaseBuffer(regpagebuf);
        //todo reg page checks?
    }

    ReleaseBuffer(metabuf);
}

/*
 * Check if the index tuple was moved concurrently to another page.
 *
 * Sometimes we need to check if a tuple was moved by a concurrent update,
 * and if so, we need to do retry.
 */
bool index_tuple_was_moved_to_another_page(Buffer revmapbuf, uint32 revmapIdx, BlockNumber oldbn) {
    ItemPointerData *revmaptids;
    RevmapContents *contents;
    ItemPointerData *tid;
    bool moved;

    LockBuffer(revmapbuf, BUFFER_LOCK_SHARE);
    contents = (RevmapContents *) PageGetContents(BufferGetPage(revmapbuf));
    revmaptids = contents->rm_tids;
    tid = revmaptids + revmapIdx;

    /*
     * We hold ShareUpdateExclusiveLock and have already seen the tid is valid,
     * so tid couldn't be invalid now
     */
    if (!ItemPointerIsValid(tid)) {
        //todo fix ereport message, or use warn and let retry here?
        ereport(ERROR,
                (errcode(ERRCODE_DATA_CORRUPTED),
                        errmsg("index is corrupted - range was desummarized concurrently with the index check")));
    }

    moved = ItemPointerGetBlockNumber(tid) != oldbn;
    LockBuffer(revmapbuf, BUFFER_LOCK_UNLOCK);
    return moved;
}

void check_all_heap_consistent(Relation idxrel, Relation heaprel, BrinCheckState *state) {
    double reltuples;
    IndexInfo *indexInfo;
    Snapshot snapshot;
    TableScanDesc scan;

    for (AttrNumber attno = 1; attno <= state->natts; attno++) {
        FmgrInfo *tmp;

        tmp = index_getprocinfo(idxrel, attno, BRIN_PROCNUM_CONSISTENT);
        fmgr_info_copy(&state->consistentFn[attno - 1], tmp, CurrentMemoryContext);

        state->scanKeys[attno - 1] = prepare_scan_key(state, attno);
    }

    snapshot = RegisterSnapshot(GetTransactionSnapshot());
    scan = table_beginscan_strat(state->heaprel,
                                 snapshot,
                                 0,
                                 NULL,
                                 true,
                                 false);

    indexInfo = BuildIndexInfo(idxrel);
    reltuples = table_index_build_scan(heaprel, idxrel, indexInfo, false, true,
                                       brin_check_callback, (void *) state, scan);

    elog(DEBUG1, "ranges were checked: %f", state->rangeCount);
    elog(DEBUG1, "scan total tuples: %f", reltuples);
    elog(DEBUG1, "invalid count: %f", state->invalidCount);

    if (snapshot != SnapshotAny)
        UnregisterSnapshot(snapshot);
}

ScanKey prepare_scan_key(const BrinCheckState *state, AttrNumber attno) {
    ScanKey scanKey;
    Oid opOid;
    Oid opFamilyOid;
    bool defined;
    StrategyNumber strategy;
    RegProcedure opRegProc;
    String *equals = makeString("=");
    List *operName = list_make1(equals);
    int attindex = attno - 1;
    Form_pg_attribute attr = TupleDescAttr(state->bdesc->bd_tupdesc, attindex);
    Oid type = attr->atttypid;

    opFamilyOid = state->idxrel->rd_opfamily[attindex];
    opOid = OperatorLookup(operName, type, type, &defined);
    strategy = get_op_opfamily_strategy(opOid, opFamilyOid);
    opRegProc = get_opcode(opOid);

    scanKey = palloc0(sizeof(ScanKeyData));

    ScanKeyEntryInitialize(
            scanKey,
            0,
            attno,
            strategy,
            type,
            attr->attcollation,
            opRegProc,
            (Datum) NULL
    );

    pfree(operName);
    pfree(equals);
    return scanKey;
}

void brin_check_callback(Relation index, ItemPointer tid, Datum *values, bool *isnull, bool tupleIsAlive, void *brstate) {
    BrinCheckState *state;
    BlockNumber heapblk;

    state = (BrinCheckState *) brstate;
    heapblk = ItemPointerGetBlockNumber(tid);

    /*
     * If we ran out of current range than are ready to validate all_nulls field of current range
     *  and move further
    */
    if (heapblk >= state->nextRangeStartBlockNumber) {
        BrinTuple *tup;
        BrinTuple *btup = NULL;
        MemoryContext oldCtx;
        OffsetNumber off;
        Size size;
        Size btupsz = 0;

        /* Validate all_nulls for current range */
        if (state->dtupvalid && !state->dtup->bt_placeholder) {
            for (int attindex = 0; attindex < state->natts; ++attindex) {

                /* Index says there is only nulls within the range, but we saw some nonnull values */
                if (state->dtup->bt_columns[attindex].bv_allnulls && !state->rangeAllNulls[attindex])
                {
                    ereport(ERROR,
                            (errcode(ERRCODE_DATA_CORRUPTED),
                                    errmsg("index is corrupted - range marked as all nulls, but contains nonnull values")));
                }
            }
        }

        MemoryContextReset(state->brinRangeCtx);
        oldCtx = MemoryContextSwitchTo(state->brinRangeCtx);

        state->rangeCount++;

        /* Reset range check aggregates */
        memset(state->rangeAllNulls, true, state->natts * sizeof(bool));

        /*
         * Move to the range that contains current heap tuple
         * We may be going over some ranges here, but that's okay because we won't be able to test it anyway
        */
        tup = brinGetTupleForHeapBlock(state->revmap, heapblk, &state->buf,
                                       &off, &size, BUFFER_LOCK_SHARE);

        if (tup) {
            btup = brin_copy_tuple(tup, size, btup, &btupsz);
            LockBuffer(state->buf, BUFFER_LOCK_UNLOCK);
            state->dtup = brin_deform_tuple(state->bdesc, btup, state->dtup);
            state->dtupvalid = true;
        } else {
            state->dtupvalid = false;
        }

        state->nextRangeStartBlockNumber = (heapblk / state->pagesPerRange + 1) * state->pagesPerRange;

        MemoryContextSwitchTo(oldCtx);

        /* Range must not be empty because we have at least one heap tuple for this range. */
        if (state->dtupvalid && state->dtup->bt_empty_range)
        {
            ereport(ERROR,
                    (errcode(ERRCODE_DATA_CORRUPTED),
                            errmsg("index is corrupted - range marked as empty but contains qualified tuples")));
        }

    }

    /* Check tuple match index values */
    if (state->dtupvalid && !state->dtup->bt_placeholder){
        check_heap_tuple(state, values, isnull);
    }

}

void check_heap_tuple(BrinCheckState *state, const Datum *values, const bool *nulls) {
    int attindex;
    BrinMemTuple *dtup = state->dtup;
    BrinDesc *bdesc = state->bdesc;
    MemoryContext oldCtx;


    MemoryContextReset(state->heapTupleCtx);
    oldCtx = MemoryContextSwitchTo(state->heapTupleCtx);

    for (attindex = 0; attindex < bdesc->bd_tupdesc->natts; attindex++) {
        BrinValues *bval;
        Datum tupCheckResult;
        bool consistent;
        ScanKey scanKey;

        scanKey = state->scanKeys[attindex];
        scanKey->sk_argument = values[attindex];
        bval = &dtup->bt_columns[attindex];

        if (bdesc->bd_info[attindex]->oi_regular_nulls && nulls[attindex])
        {
            if (!bval->bv_hasnulls) {
                ///todo add error details
                ereport(ERROR,
                        (errcode(ERRCODE_DATA_CORRUPTED),
                                errmsg("index is corrupted - hasnull = false when there is a null values")));
            }
            elog(DEBUG1, "check value: null");
            continue;
        }

        state->rangeAllNulls[attindex] = false;

        if (state->consistentFn[attindex].fn_nargs >= 4)
        {
            tupCheckResult = FunctionCall4Coll(&state->consistentFn[attindex],
                                               state->idxrel->rd_indcollation[attindex],
                                               PointerGetDatum(state->bdesc),
                                               PointerGetDatum(bval),
                                               PointerGetDatum(&scanKey),
                                               Int32GetDatum(1)
            );
            consistent = DatumGetBool(tupCheckResult);
        } else {

            tupCheckResult = FunctionCall3Coll(&state->consistentFn[attindex],
                                               state->idxrel->rd_indcollation[attindex],
                                               PointerGetDatum(state->bdesc),
                                               PointerGetDatum(bval),
                                               PointerGetDatum(scanKey)
            );

            consistent = DatumGetBool(tupCheckResult);
        }



        if (!consistent)
        {
            ///todo add error details
            state->invalidCount++;
            elog(DEBUG1, "value %d: not consistent", values[attindex]);
//            ereport(ERROR,
//                    (errcode(ERRCODE_DATA_CORRUPTED),
//                            errmsg("index is corrupted")));
        }

    }

    MemoryContextSwitchTo(oldCtx);
}

/*
 * PageGetItemId() wrapper that validates returned line pointer.
 *
 * itemId in brin index could be UNUSED or NORMAL.
 */
ItemId PageGetItemIdCareful(BrinCheckState *state, BlockNumber block, Page page, OffsetNumber offset) {
    ItemId		itemid = PageGetItemId(page, offset);

    if (ItemIdGetOffset(itemid) + ItemIdGetLength(itemid) >
        BLCKSZ - MAXALIGN(sizeof(BrinSpecialSpace)))
        ereport(ERROR,
                (errcode(ERRCODE_INDEX_CORRUPTED),
                        errmsg("line pointer points past end of tuple space in index \"%s\"",
                               RelationGetRelationName(state->idxrel)),
                        errdetail_internal("Index tid=(%u,%u) lp_off=%u, lp_len=%u lp_flags=%u.",
                                           block, offset, ItemIdGetOffset(itemid),
                                           ItemIdGetLength(itemid),
                                           ItemIdGetFlags(itemid))));


    /* Verify that line pointer is LP_NORMAL or LP_UNUSED */
    if (!((ItemIdIsNormal(itemid) && ItemIdGetLength(itemid) != 0) ||
          (!ItemIdIsUsed(itemid) && ItemIdGetLength(itemid) == 0)))
    {
        ereport(ERROR,
                (errcode(ERRCODE_INDEX_CORRUPTED),
                        errmsg("invalid line pointer storage in index \"%s\"",
                               RelationGetRelationName(state->idxrel)),
                        errdetail_internal("Index tid=(%u,%u) lp_off=%u, lp_len=%u lp_flags=%u.",
                                           block, offset, ItemIdGetOffset(itemid),
                                           ItemIdGetLength(itemid),
                                           ItemIdGetFlags(itemid))));
    }

    return itemid;
}
