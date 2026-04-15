pg_async_test_sources = files(
    'pg_async_notify_test-v24.c'
)
pg_async_test = executable('pg_async_notify_test',
    pg_async_test_sources,
    dependencies: [frontend_code, libpq, thread_dep, os_deps],
    kwargs: default_bin_args,
)

bin_targets += pg_async_test