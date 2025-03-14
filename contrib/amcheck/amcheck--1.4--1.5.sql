/* contrib/amcheck/amcheck--1.4--1.5.sql */

-- complain if script is sourced in psql, rather than via CREATE EXTENSION
\echo Use "ALTER EXTENSION amcheck UPDATE TO '1.5'" to load this file. \quit


--
-- brin_index_check()
--
CREATE FUNCTION brin_index_check(index regclass)
RETURNS VOID
AS 'MODULE_PATHNAME', 'brin_index_check'
LANGUAGE C STRICT PARALLEL RESTRICTED;

-- We don't want this to be available to public
REVOKE ALL ON FUNCTION brin_index_check(regclass) FROM PUBLIC;
