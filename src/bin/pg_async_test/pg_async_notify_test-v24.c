/*
 * Platform detection for I/O multiplexing.
 *
 * To manually override, add one of these at the very top of this file:
 *   #define USE_KQUEUE    (requires kqueue support: macOS, FreeBSD, etc.)
 *   #define USE_PPOLL     (requires ppoll support: Linux, etc.)
 *
 * Note: Ensure the chosen method is available on your platform, or you'll
 * get compilation errors.
 */
#include "../../interfaces/libpq/libpq-fe.h"
#if !defined(USE_KQUEUE) && !defined(USE_PPOLL)
# if defined(__APPLE__) || defined(__FreeBSD__) || defined(__OpenBSD__) || defined(__NetBSD__)
#  define USE_KQUEUE
# else
#  define USE_PPOLL
# endif
#endif

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#ifdef USE_KQUEUE
#include <sys/event.h>
#endif
#ifdef USE_PPOLL
#include <poll.h>
#endif
#include <sys/time.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>
#include <stdint.h>
#include <getopt.h>
#include <pthread.h>
#include <math.h>

#include "libpq-fe.h"

#define PG_TIME_GET_DOUBLE(t) (0.000001 * (t))
#define CONNECTION_STRING "postgresql://localhost:5432/postgres"
#define MAX_NOTIFIERS 256  /* Maximum notifiers per channel for sequence tracking */

/* Latency histogram buckets */
#define NUM_BUCKETS 6
static uint64_t bucket_counts[NUM_BUCKETS];
static uint64_t bucket_totals[NUM_BUCKETS];  /* Total latency in microseconds */
static pthread_mutex_t histogram_mutex = PTHREAD_MUTEX_INITIALIZER;

static uint32_t num_notifies_sent;
static uint32_t num_notifies_received;
static volatile int start_notifying = 0;  /* Signal for notifiers to start */

/* Synchronization for listener LISTEN setup */
static int listeners_ready = 0;
static pthread_mutex_t startup_mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t startup_cond = PTHREAD_COND_INITIALIZER;

/* --extra-channels argument */
static int			num_extra_channels = 0;

/* --sleep argument */
static double		max_sleep_seconds = 0.0;

/* --sleep-exp argument */
static double		sleep_exponential_factor = 1.0;

/* --batch argument */
static int			batch_size = 1;

/* --duration argument and shutdown flag */
static double		duration_seconds = 0.0;
static volatile int	shutdown_requested = 0;

/* --with-insert argument: prepend INSERT INTO t_<channel_id> before each NOTIFY */
static int			with_insert = 0;

/* --payload-size argument: total payload size in bytes (0 = no padding) */
static int			payload_size = 0;

/* pg_get_async_wakeup_stats availability and data */
static int has_async_wakeup_stats = 0;  /* Detected function availability */
static uint64_t async_wakeup_stats[13] = {0};  /* Latest stats snapshot */
static pthread_mutex_t wakeup_stats_mutex = PTHREAD_MUTEX_INITIALIZER;

/* Thread arguments structure */
struct thread_args {
	int channel_id;
	int notifier_id;  /* ID of notifier within channel (0 to num_notify_threads-1) */
	int num_notifiers;  /* Total number of notifiers per channel */
	int total_listeners;  /* Total number of listener threads (all channels) */
	uint64_t *seq_counter;  /* Pointer to this notifier's sequence counter */
};

typedef int64_t pg_time_usec_t;

static inline pg_time_usec_t
pg_time_now(void)
{
	struct timeval tv;

	gettimeofday(&tv, NULL);

	return (pg_time_usec_t) (tv.tv_sec * 1000000 + tv.tv_usec);
}

static void
exit_nicely(PGconn *conn)
{
	PQfinish(conn);
	exit(1);
}

static int
get_latency_bucket(double latency_ms)
{
	/* Buckets: 0-0.01ms, 0.01-0.1ms, 0.1-1ms, 1-10ms, 10-100ms, >100ms */
	if (latency_ms < 0.01)
		return 0;
	else if (latency_ms < 0.1)
		return 1;
	else if (latency_ms < 1.0)
		return 2;
	else if (latency_ms < 10.0)
		return 3;
	else if (latency_ms < 100.0)
		return 4;
	else
		return 5;
}

static void
update_histogram(uint64_t latency_usec)
{
	double latency_ms = latency_usec / 1000.0;
	int bucket = get_latency_bucket(latency_ms);

	pthread_mutex_lock(&histogram_mutex);
	bucket_counts[bucket]++;
	bucket_totals[bucket] += latency_usec;
	pthread_mutex_unlock(&histogram_mutex);
}

static int
check_async_wakeup_stats_available(void)
{
	PGconn *conn;
	PGresult *res;
	int available = 0;

	/* Make a temporary connection to check function availability */
	conn = PQconnectdb(CONNECTION_STRING);

	if (PQstatus(conn) != CONNECTION_OK)
	{
		fprintf(stderr, "%s", PQerrorMessage(conn));
		exit_nicely(conn);
	}

	/* Query pg_proc to see if the function exists in pg_catalog */
	res = PQexec(conn,
				 "SELECT 1 FROM pg_proc p "
				 "JOIN pg_namespace n ON p.pronamespace = n.oid "
				 "WHERE p.proname = 'pg_get_async_wakeup_stats' "
				 "AND n.nspname = 'pg_catalog'");

	if (PQresultStatus(res) == PGRES_TUPLES_OK && PQntuples(res) > 0)
		available = 1;

	PQclear(res);
	PQfinish(conn);

	return available;
}

static void
fetch_async_wakeup_stats(void)
{
	PGconn *conn;
	PGresult *res;

	if (!has_async_wakeup_stats)
		return;

	conn = PQconnectdb(CONNECTION_STRING);

	if (PQstatus(conn) != CONNECTION_OK)
	{
		fprintf(stderr, "%s", PQerrorMessage(conn));
		exit_nicely(conn);
	}

	res = PQexec(conn,
				 "SELECT signaled_targeted, advancing_behind, advancing_ahead, "
				 "idle_behind, avoided_wakeups, already_ahead, "
				 "necessary_wakeups, unnecessary_wakeups "
				 "FROM pg_catalog.pg_get_async_wakeup_stats()");

	if (PQresultStatus(res) == PGRES_TUPLES_OK && PQntuples(res) > 0)
	{
		pthread_mutex_lock(&wakeup_stats_mutex);
		for (int i = 0; i < 8; i++)
		{
			async_wakeup_stats[i] = strtoull(PQgetvalue(res, 0, i), NULL, 10);
		}
		pthread_mutex_unlock(&wakeup_stats_mutex);
	}

	PQclear(res);
	PQfinish(conn);
}

static void
reset_async_wakeup_stats(void)
{
	PGconn *conn;
	PGresult *res;

	conn = PQconnectdb(CONNECTION_STRING);

	if (PQstatus(conn) != CONNECTION_OK)
	{
		fprintf(stderr, "%s", PQerrorMessage(conn));
		exit_nicely(conn);
	}

	res = PQexec(conn, "SELECT pg_catalog.pg_reset_async_wakeup_stats()");

	if (PQresultStatus(res) != PGRES_TUPLES_OK)
	{
		fprintf(stderr, "Failed to reset async wakeup stats: %s",
				PQerrorMessage(conn));
	}

	PQclear(res);
	PQfinish(conn);
}

static void *
notify_thread_main(void *arg)
{
	struct thread_args *args = (struct thread_args *)arg;
	int channel_id = args->channel_id;
	int notifier_id = args->notifier_id;
	uint64_t *seq_counter = args->seq_counter;
	PGconn	   *conn;
	PGresult   *res;
	char		channel_name[32];
	char		insert_prefix[64];

	/* Generate channel name from channel_id */
	snprintf(channel_name, sizeof(channel_name), "%d", channel_id);

	/* Generate per-channel INSERT prefix */
	snprintf(insert_prefix, sizeof(insert_prefix),
			 "INSERT INTO t_%d DEFAULT VALUES; ", channel_id);

	/* Pre-generate fixed padding string for --payload-size */
	char		payload_pad[7500];
	if (payload_size > 0)
	{
		payload_pad[0] = ' ';
		memset(payload_pad + 1, 'x', payload_size - 1);
		payload_pad[payload_size] = '\0';
	}
	else
		payload_pad[0] = '\0';

	/* Make a connection to the database */
	conn = PQconnectdb(CONNECTION_STRING);

	/* Check to see that the backend connection was successfully made */
	if (PQstatus(conn) != CONNECTION_OK)
	{
		fprintf(stderr, "%s", PQerrorMessage(conn));
		exit_nicely(conn);
	}

	/* Wait for signal to start notifying */
	while (!start_notifying)
		usleep(10000);  /* Sleep 10ms */

	while (!shutdown_requested)
	{
		/* Sleep random amount if --sleep was specified */
		if (max_sleep_seconds > 0.0)
		{
			/* Calculate per-channel max sleep using exponential factor */
			double per_channel_max = max_sleep_seconds * pow(sleep_exponential_factor, channel_id);

			double random_sleep = ((double)rand() / RAND_MAX) * per_channel_max;
			struct timespec ts;
			ts.tv_sec = (time_t)random_sleep;
			ts.tv_nsec = (long)((random_sleep - ts.tv_sec) * 1000000000.0);

			if (nanosleep(&ts, NULL) == -1)
			{
				fprintf(stderr, "Channel %d notifier %d: nanosleep failed: ",
						channel_id, notifier_id);
				switch (errno)
				{
					case EINVAL:
						fprintf(stderr, "EINVAL - invalid timespec (tv_sec=%ld, tv_nsec=%ld)\n",
								(long)ts.tv_sec, ts.tv_nsec);
						fprintf(stderr, "  random_sleep value was: %.6f seconds\n", random_sleep);
						fprintf(stderr, "  This likely indicates overflow in sleep calculation.\n");
						break;
					case EINTR:
						fprintf(stderr, "EINTR - interrupted by signal\n");
						break;
					case EFAULT:
						fprintf(stderr, "EFAULT - problem copying from user space\n");
						break;
					default:
						fprintf(stderr, "Unknown error (errno=%d)\n", errno);
						break;
				}
				exit_nicely(conn);
			}
		}

		/* Start transaction if batching */
		if (batch_size > 1)
		{
			res = PQexec(conn, "BEGIN");
			if (PQresultStatus(res) != PGRES_COMMAND_OK)
			{
				fprintf(stderr, "BEGIN command failed: %s", PQerrorMessage(conn));
				PQclear(res);
				exit_nicely(conn);
			}
			PQclear(res);
		}

		/* Send batch_size notifications */
		for (int i = 0; i < batch_size; i++)
		{
			char buf[8192 + 128];
			pg_time_usec_t send_time;
			uint64_t seq;

			/* Get timestamp before sending */
			send_time = pg_time_now();

			/* Atomically get and increment this notifier's sequence counter */
			seq = __sync_fetch_and_add(seq_counter, 1);

			/* Send notification with notifier_id, sequence number, and timestamp */
			snprintf(buf, sizeof(buf), "%sNOTIFY \"%s\", '%d %lld %lld%s'",
					 with_insert ? insert_prefix : "",
					 channel_name, notifier_id, (long long)seq, (long long)send_time,
					 payload_pad);
			res = PQexec(conn, buf);
			if (PQresultStatus(res) != PGRES_COMMAND_OK)
			{
				fprintf(stderr, "NOTIFY command failed: %s", PQerrorMessage(conn));
				PQclear(res);
				exit_nicely(conn);
			}
			PQclear(res);

			__sync_fetch_and_add(&num_notifies_sent, 1);
		}

		/* Commit transaction if batching */
		if (batch_size > 1)
		{
			res = PQexec(conn, "COMMIT");
			if (PQresultStatus(res) != PGRES_COMMAND_OK)
			{
				fprintf(stderr, "COMMIT command failed: %s", PQerrorMessage(conn));
				PQclear(res);
				exit_nicely(conn);
			}
			PQclear(res);
		}
	}

	return NULL;
}

static void *
listen_thread_main(void *arg)
{
	struct thread_args *args = (struct thread_args *)arg;
	int channel_id = args->channel_id;
	int num_notifiers = args->num_notifiers;
	PGconn	   *conn;
	PGresult   *res;
	PGnotify   *notify;
	uint64_t	expected_seq[MAX_NOTIFIERS];
	char		channel_name[32];
	char		listen_cmd[64];

	/* Initialize expected sequence for each notifier */
	for (int i = 0; i < MAX_NOTIFIERS; i++)
		expected_seq[i] = 0;

	/* Generate channel name from channel_id */
	snprintf(channel_name, sizeof(channel_name), "%d", channel_id);

	/* Make a connection to the database */
	conn = PQconnectdb(CONNECTION_STRING);

	/* Check to see that the backend connection was successfully made */
	if (PQstatus(conn) != CONNECTION_OK)
	{
		fprintf(stderr, "%s", PQerrorMessage(conn));
		exit_nicely(conn);
	}


	/*
	 * Issue LISTEN command for "extra" channels. The extra channels are never
	 * notified, they're used just to bloat the list of channels that notify
	 * processing needs to traverse.
	 */
	for (int i = 0; i < num_extra_channels; i++)
	{
		snprintf(listen_cmd, sizeof(listen_cmd), "LISTEN \"extra%d\"", i);
		res = PQexec(conn, listen_cmd);
		if (PQresultStatus(res) != PGRES_COMMAND_OK)
		{
			fprintf(stderr, "LISTEN command failed: %s", PQerrorMessage(conn));
			PQclear(res);
			exit_nicely(conn);
		}
		PQclear(res);
	}

	/*
	 * Issue LISTEN command to enable notifications from the rule's NOTIFY.
	 */
	snprintf(listen_cmd, sizeof(listen_cmd), "LISTEN \"%s\"", channel_name);
	res = PQexec(conn, listen_cmd);
	if (PQresultStatus(res) != PGRES_COMMAND_OK)
	{
		fprintf(stderr, "LISTEN command failed: %s", PQerrorMessage(conn));
		PQclear(res);
		exit_nicely(conn);
	}
	PQclear(res);

	/* Signal that this listener is ready */
	pthread_mutex_lock(&startup_mutex);
	listeners_ready++;
	if (listeners_ready == args->total_listeners)
		pthread_cond_signal(&startup_cond);  /* Wake main thread if we're the last */
	pthread_mutex_unlock(&startup_mutex);

	while (!shutdown_requested)
	{
		/*
		 * Sleep until something happens on the connection.  We use kqueue(2)
		 * on macOS/BSD for better performance and scalability, or ppoll(2) on
		 * other platforms. Both avoid the FD_SETSIZE limitation of select().
		 */
		int			sock;

		sock = PQsocket(conn);

		if (sock < 0)
			break;				/* shouldn't happen */

#ifdef USE_KQUEUE
		/* Use kqueue for better performance and scalability */
		int kq;
		struct kevent kev;
		struct kevent event;

		kq = kqueue();
		if (kq < 0)
		{
			fprintf(stderr, "kqueue() failed: %s\n", strerror(errno));
			exit_nicely(conn);
		}

		/* Monitor the socket for read events */
		EV_SET(&kev, sock, EVFILT_READ, EV_ADD | EV_ONESHOT, 0, 0, NULL);

		/* Wait with timeout to allow periodic shutdown checks */
		struct timespec timeout;
		timeout.tv_sec = 0;
		timeout.tv_nsec = 100000000;  /* 100ms */

		int ret = kevent(kq, &kev, 1, &event, 1, &timeout);
		if (ret < 0)
		{
			fprintf(stderr, "kevent() failed: %s\n", strerror(errno));
			close(kq);
			exit_nicely(conn);
		}

		close(kq);

		/* If timeout or shutdown requested, continue to check */
		if (ret == 0 || shutdown_requested)
			continue;
#elif defined(USE_PPOLL)
		/* Use ppoll (nanosecond resolution) */
		struct pollfd pfd;

		pfd.fd = sock;
		pfd.events = POLLIN;
		pfd.revents = 0;

		/* Wait with timeout to allow periodic shutdown checks */
		struct timespec timeout;
		timeout.tv_sec = 0;
		timeout.tv_nsec = 100000000;  /* 100ms */

		int ret = ppoll(&pfd, 1, &timeout, NULL);
		if (ret < 0)
		{
			fprintf(stderr, "ppoll() failed: %s\n", strerror(errno));
			exit_nicely(conn);
		}

		/* If timeout or shutdown requested, continue to check */
		if (ret == 0 || shutdown_requested)
			continue;
#else
# error "No I/O multiplexing method defined. Define USE_KQUEUE or USE_PPOLL."
#endif

		/* Now check for input */
		PQconsumeInput(conn);
		while ((notify = PQnotifies(conn)) != NULL)
		{
			pg_time_usec_t recv_time;
			pg_time_usec_t send_time;
			int notifier_id;
			uint64_t seq;
			uint64_t latency_usec;

			/* Get receive timestamp */
			recv_time = pg_time_now();

			/* Parse notifier_id, sequence number, and send timestamp from payload */
			if (notify->extra && notify->extra[0])
			{
				if (sscanf(notify->extra, "%d %lld %lld", &notifier_id, (long long *)&seq, (long long *)&send_time) == 3)
				{
					/* Validate notifier_id */
					if (notifier_id < 0 || notifier_id >= num_notifiers)
					{
						fprintf(stderr, "\nERROR: Channel %d received invalid notifier_id %d (expected 0-%d)\n",
								channel_id, notifier_id, num_notifiers - 1);
						abort();
					}

					/* Verify sequence number for this notifier */
					if (seq != expected_seq[notifier_id])
					{
						fprintf(stderr, "\nERROR: Channel %d notifier %d sequence gap! Expected %lld, received %lld\n",
								channel_id, notifier_id, (long long)expected_seq[notifier_id], (long long)seq);
						abort();
					}
					expected_seq[notifier_id]++;

					latency_usec = recv_time - send_time;

					/* Update histogram */
					update_histogram(latency_usec);
				}
			}

			PQfreemem(notify);
			PQconsumeInput(conn);

			__sync_fetch_and_add(&num_notifies_received, 1);
		}
	}

	return NULL;
}

static void
print_usage(const char *progname)
{
	printf("Usage: %s [OPTIONS]\n\n", progname);
	printf("PostgreSQL Async Notify Performance Test\n\n");
	printf("Tests PostgreSQL LISTEN/NOTIFY performance with configurable threads and channels.\n");
	printf("Connects to: %s\n\n", CONNECTION_STRING);
	printf("Options:\n");
	printf("  --listeners THREADS       Number of listener threads per channel\n");
	printf("                           (default: 1, minimum: 1)\n\n");
	printf("  --notifiers THREADS       Number of notifier threads per channel\n");
	printf("                           (default: 1, minimum: 1)\n\n");
	printf("  --channels COUNT          Number of channels to create and test\n");
	printf("                           (default: 1, minimum: 1)\n\n");
	printf("  --extra-channels COUNT    Additional channels to listen on for load testing\n");
	printf("                           (default: 0, minimum: 0)\n");
	printf("                           Note: extra channels are not notified\n\n");
	printf("  --sleep SECONDS          Maximum random sleep before each notify\n");
	printf("                           (default: 0.0, minimum: 0.0)\n");
	printf("                           Supports fractional values (e.g., 0.1 for 100ms)\n\n");
	printf("  --sleep-exp FACTOR       Exponential scaling factor for per-channel sleep\n");
	printf("                           (default: 1.0, must be > 0.0)\n");
	printf("                           Channel N gets: --sleep * FACTOR^N\n");
	printf("                           Use <1.0 to decrease sleep for higher channels\n");
	printf("                           Use >1.0 to increase sleep for higher channels\n\n");
	printf("  --batch COUNT            Number of NOTIFYs to send in a single transaction\n");
	printf("                           (default: 1, minimum: 1)\n");
	printf("                           Each NOTIFY has its own seq and send_time\n");
	printf("                           BEGIN/COMMIT only used when COUNT > 1\n\n");
	printf("  --duration SECONDS       Run for specified time then exit gracefully\n");
	printf("                           (default: 0 = run forever, must be > 0.0)\n");
	printf("                           Supports fractional values (e.g., 10.5)\n\n");
	printf("  --with-insert            Prepend INSERT INTO t_<channel_id> DEFAULT VALUES before each NOTIFY\n");
	printf("                           (default: off). Creates one table per channel at startup\n");
	printf("                           and runs INSERT+NOTIFY in one statement.\n\n");
	printf("  --payload-size BYTES     Append BYTES of padding to NOTIFY payload (0-7900)\n");
	printf("                           (default: 0 = no padding, ~30-50 bytes natural payload)\n");
	printf("                           Capped at 7900 to leave room for useful payload.\n\n");
	printf("  --help                   Display this help message and exit\n\n");
	exit(0);
}

static void create_test_tables(int num_channels)
{
	PGconn		*conn;
	PGresult	*res;
	char		buf[256];

	conn = PQconnectdb(CONNECTION_STRING);
	if (PQstatus(conn) != CONNECTION_OK)
	{
		fprintf(stderr, "%s", PQerrorMessage(conn));
		exit_nicely(conn);
	}

	for (int i = 0; i < num_channels; i++)
	{
		snprintf(buf, sizeof(buf),
				 "CREATE TABLE IF NOT EXISTS t_%d (a bigserial); TRUNCATE TABLE t_%d;",
				 i, i);
		res = PQexec(conn, buf);
		if (PQresultStatus(res) != PGRES_COMMAND_OK)
		{
			fprintf(stderr, "CREATE TABLE t_%d failed: %s", i, PQerrorMessage(conn));
			PQclear(res);
			exit_nicely(conn);
		}
		PQclear(res);
	}

	fprintf(stderr, "Created %d test tables (t_0 .. t_%d)\n", num_channels, num_channels - 1);
	PQfinish(conn);
}

int
main(int argc, char **argv)
{
	int			num_threads = 0;
	pthread_t  *threads;
	pg_time_usec_t start;
	static struct option long_options[] = {
		/* systematic long/short named options */
		{"listeners", required_argument, NULL, 1},
		{"notifiers", required_argument, NULL, 2},
		{"channels", required_argument, NULL, 3},
		{"extra-channels", required_argument, NULL, 4},
		{"sleep", required_argument, NULL, 5},
		{"sleep-exp", required_argument, NULL, 7},
		{"batch", required_argument, NULL, 6},
		{"duration", required_argument, NULL, 8},
		{"with-insert", no_argument, NULL, 9},
		{"payload-size", required_argument, NULL, 10},
		{"help", no_argument, NULL, 'h'},
		{NULL, 0, NULL, 0}
	};
	int			num_listen_threads = 1;
	int			num_notify_threads = 1;
	int			num_channels = 1;
	int			optindex;
	int			c;

	while ((c = getopt_long(argc, argv, "", long_options, &optindex)) != -1)
	{
		switch (c)
		{
			case 1:				/* listeners */
				num_listen_threads = atoi(optarg);
				if (num_listen_threads < 1)
				{
					fprintf(stderr, "invalid --listeners argument\n");
					exit(1);
				}
				break;

			case 2:				/* notifiers */
				num_notify_threads = atoi(optarg);
				if (num_notify_threads < 1)
				{
					fprintf(stderr, "invalid --notifiers argument\n");
					exit(1);
				}
				break;

			case 3:				/* channels */
				num_channels = atoi(optarg);
				if (num_channels < 1)
				{
					fprintf(stderr, "invalid --channels argument\n");
					exit(1);
				}
				break;

			case 4:				/* extra-channels */
				num_extra_channels = atoi(optarg);
				if (num_extra_channels < 0)
				{
					fprintf(stderr, "invalid --extra-channels argument\n");
					exit(1);
				}
				break;

			case 5:				/* sleep */
				max_sleep_seconds = atof(optarg);
				if (max_sleep_seconds < 0.0)
				{
					fprintf(stderr, "invalid --sleep argument\n");
					exit(1);
				}
				break;

			case 6:				/* batch */
				batch_size = atoi(optarg);
				if (batch_size < 1)
				{
					fprintf(stderr, "invalid --batch argument (minimum: 1)\n");
					exit(1);
				}
				break;

			case 7:				/* sleep-exp */
				sleep_exponential_factor = atof(optarg);
				if (sleep_exponential_factor <= 0.0)
				{
					fprintf(stderr, "invalid --sleep-exp argument (must be > 0.0)\n");
					exit(1);
				}
				break;

			case 8:				/* duration */
				duration_seconds = atof(optarg);
				if (duration_seconds <= 0.0)
				{
					fprintf(stderr, "invalid --duration argument (must be > 0.0)\n");
					exit(1);
				}
				break;

			case 9:				/* with-insert */
				with_insert = 1;
				break;

			case 10:			/* payload-size */
				payload_size = atoi(optarg);
				/*
				 * Postgres NOTIFY payload limit is 8000 bytes. We cap at 7900
				 * because this padding is appended on top of the useful payload
				 * (~30-50 bytes: notifier_id, sequence number, timestamp).
				 */
				if (payload_size < 0 || payload_size > 7900)
				{
					fprintf(stderr, "invalid --payload-size argument (0-7900)\n");
					exit(1);
				}
				break;

			case 'h':				/* help */
				print_usage(argv[0]);
				break;

			case '?':				/* unknown option or missing argument */
				fprintf(stderr, "Error: Unknown option or missing argument\n\n");
				print_usage(argv[0]);
				break;

			default:
				fprintf(stderr, "Error: Unexpected getopt_long return value\n");
				exit(1);
		}
	}

	/* Check for extra positional arguments */
	if (optind < argc)
	{
		fprintf(stderr, "Error: Unexpected argument '%s'\n\n", argv[optind]);
		print_usage(argv[0]);
	}

	if (with_insert)
		create_test_tables(num_channels);

	/* Check if pg_get_async_wakeup_stats is available */
	has_async_wakeup_stats = check_async_wakeup_stats_available();
	if (has_async_wakeup_stats)
		reset_async_wakeup_stats();

	int total_threads = num_channels * (num_notify_threads + num_listen_threads);
	threads = malloc(total_threads * sizeof(pthread_t));
	struct thread_args *thread_args_array = malloc(total_threads * sizeof(struct thread_args));

	/* Allocate sequence counters for each notifier thread (initialized to 0) */
	uint64_t *notifier_seqs = calloc(num_channels * num_notify_threads, sizeof(uint64_t));

	/* Spawn threads for each channel */
	for (int channel_id = 0; channel_id < num_channels; channel_id++)
	{
		/* Spawn notifier threads for this channel */
		for (int i = 0; i < num_notify_threads; i++)
		{
			int			s;
			int			notifier_index = channel_id * num_notify_threads + i;

			thread_args_array[num_threads].channel_id = channel_id;
			thread_args_array[num_threads].notifier_id = i;
			thread_args_array[num_threads].num_notifiers = num_notify_threads;
			thread_args_array[num_threads].total_listeners = num_channels * num_listen_threads;
			thread_args_array[num_threads].seq_counter = &notifier_seqs[notifier_index];
			s = pthread_create(&threads[num_threads], NULL,
							   &notify_thread_main, &thread_args_array[num_threads]);
			if (s != 0)
			{
				fprintf(stderr, "pthread_create failed\n");
				exit(1);
			}
			num_threads++;
		}

		/* Spawn listener threads for this channel */
		for (int i = 0; i < num_listen_threads; i++)
		{
			int			s;

			thread_args_array[num_threads].channel_id = channel_id;
			thread_args_array[num_threads].notifier_id = -1;  /* Not used for listeners */
			thread_args_array[num_threads].num_notifiers = num_notify_threads;
			thread_args_array[num_threads].total_listeners = num_channels * num_listen_threads;
			thread_args_array[num_threads].seq_counter = NULL;  /* Not used for listeners */
			s = pthread_create(&threads[num_threads], NULL,
							   &listen_thread_main, &thread_args_array[num_threads]);
			if (s != 0)
			{
				fprintf(stderr, "pthread_create failed\n");
				exit(1);
			}
			num_threads++;
		}
	}

	/* Wait for all listeners to establish LISTEN before notifiers start sending */
	pthread_mutex_lock(&startup_mutex);
	while (listeners_ready < num_channels * num_listen_threads)
		pthread_cond_wait(&startup_cond, &startup_mutex);
	pthread_mutex_unlock(&startup_mutex);

	/* Signal notifiers to start */
	start_notifying = 1;

	start = pg_time_now();

	uint32_t prev_sent = 0;
	uint32_t prev_received = 0;
	int first_iteration = 1;

	while (!shutdown_requested)
	{
		double		elapsed_sec;
		uint32_t	curr_sent;
		uint32_t	curr_received;
		uint32_t	sent_per_sec;
		uint32_t	received_per_sec;

		sleep(1);

		/* Fetch async wakeup stats if available */
		fetch_async_wakeup_stats();

		/* Move cursor back up before printing (except first time) */
		if (!first_iteration)
		{
			int lines = NUM_BUCKETS + 2;  /* Latency distribution */
			if (has_async_wakeup_stats)
				lines += 12;  /* 8 for SignalBackends + 4 for asyncQueueReadAllNotifications */
			fprintf(stderr, "\033[%dA\r", lines);
		}
		first_iteration = 0;

		elapsed_sec = PG_TIME_GET_DOUBLE(pg_time_now() - start);

		curr_sent = num_notifies_sent;
		curr_received = num_notifies_received;
		sent_per_sec = curr_sent - prev_sent;
		received_per_sec = curr_received - prev_received;

		/* Print stats on same line */
		fprintf(stderr, "\r%.0f s: %u sent (%u/s), %u received (%u/s)    ",
				elapsed_sec, curr_sent, sent_per_sec, curr_received, received_per_sec);

		/* Print histogram */
		pthread_mutex_lock(&histogram_mutex);

		uint64_t total_measured = 0;
		for (int i = 0; i < NUM_BUCKETS; i++)
			total_measured += bucket_counts[i];

		if (total_measured > 0)
		{
			const char *bucket_labels[] = {
				" 0.00-0.01ms   ",
				" 0.01-0.10ms   ",
				" 0.10-1.00ms   ",
				" 1.00-10.00ms  ",
				" 10.00-100.00ms",
				">100.00ms     "
			};

			fprintf(stderr, "\n");
			fprintf(stderr, "Notification Latency Distribution:\n");
			for (int i = 0; i < NUM_BUCKETS; i++)
			{
				uint64_t count = bucket_counts[i];
				double percentage = (count * 100.0) / total_measured;
				double avg_latency_ms = 0.0;

				if (count > 0)
					avg_latency_ms = (bucket_totals[i] / 1000.0) / count;

				/* Draw bar chart (max 10 chars) */
				int bar_length = (int)((count * 10) / total_measured);
				if (bar_length == 0 && count > 0)
					bar_length = 1;

				fprintf(stderr, "%s  ", bucket_labels[i]);
				for (int j = 0; j < bar_length; j++)
					fprintf(stderr, "#");
				for (int j = bar_length; j < 10; j++)
					fprintf(stderr, " ");

				fprintf(stderr, " %llu (%.1f%%) avg: %.3fms\n",
						(unsigned long long)count, percentage, avg_latency_ms);
			}
		}

		pthread_mutex_unlock(&histogram_mutex);

		/* Display async wakeup stats if available */
		if (has_async_wakeup_stats)
		{
			pthread_mutex_lock(&wakeup_stats_mutex);

			uint64_t stats[8];
			memcpy(stats, async_wakeup_stats, sizeof(stats));

			pthread_mutex_unlock(&wakeup_stats_mutex);

			/* First histogram: SignalBackends Statistics */
			uint64_t signal_total = stats[0] + stats[1] + stats[2] + stats[3] + stats[4] + stats[5];

			if (signal_total > 0)
			{
				const char *signal_labels[] = {
					"signaled_targeted",
					"advancing_behind ",
					"advancing_ahead  ",
					"idle_behind      ",
					"avoided_wakeups  ",
					"already_ahead    "
				};
				int signal_indices[] = {0, 1, 2, 3, 4, 5};

				fprintf(stderr, "\n");
				fprintf(stderr, "SignalBackends Statistics:\n");
				for (int i = 0; i < 6; i++)
				{
					int idx = signal_indices[i];
					double percentage = (stats[idx] * 100.0) / signal_total;

					/* Draw bar chart (max 10 chars) */
					int bar_length = (int)((stats[idx] * 10) / signal_total);
					if (bar_length == 0 && stats[idx] > 0)
						bar_length = 1;

					fprintf(stderr, "%s  ", signal_labels[i]);
					for (int j = 0; j < bar_length; j++)
						fprintf(stderr, "#");
					for (int j = bar_length; j < 10; j++)
						fprintf(stderr, " ");

					fprintf(stderr, " %llu (%.1f%%)\n",
							(unsigned long long)stats[idx], percentage);
				}
			}

			/* Second histogram: asyncQueueReadAllNotifications Statistics */
			uint64_t asyncq_total = stats[6] + stats[7];

			if (asyncq_total > 0)
			{
				const char *asyncq_labels[] = {
					"necessary_wakeups  ",
					"unnecessary_wakeups"
				};
				int asyncq_indices[] = {6, 7};

				fprintf(stderr, "\n");
				fprintf(stderr, "asyncQueueReadAllNotifications Statistics:\n");
				for (int i = 0; i < 2; i++)
				{
					int idx = asyncq_indices[i];
					double percentage = (stats[idx] * 100.0) / asyncq_total;

					/* Draw bar chart (max 10 chars) */
					int bar_length = (int)((stats[idx] * 10) / asyncq_total);
					if (bar_length == 0 && stats[idx] > 0)
						bar_length = 1;

					fprintf(stderr, "%s  ", asyncq_labels[i]);
					for (int j = 0; j < bar_length; j++)
						fprintf(stderr, "#");
					for (int j = bar_length; j < 10; j++)
						fprintf(stderr, " ");

					fprintf(stderr, " %llu (%.1f%%)\n",
							(unsigned long long)stats[idx], percentage);
				}
			}
		}

		fflush(stderr);

		prev_sent = curr_sent;
		prev_received = curr_received;

		/* Check if duration has elapsed */
		if (duration_seconds > 0.0)
		{
			elapsed_sec = PG_TIME_GET_DOUBLE(pg_time_now() - start);
			if (elapsed_sec > duration_seconds)
				exit(0);
		}

	}

	return 0;
}
