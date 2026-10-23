set(jbmc_strings_cmdline
    "$<TARGET_FILE:jbmc> --validate-goto-model --validate-ssa-equation")
set(jbmc_strings_shards 4)

# The plain (non-symex-driven) CORE run of this suite is one of the slowest
# non-sharded CORE ctests; shard it (keeping its 30-minute per-shard timeout)
# so it runs as several parallel ctest entries on the macOS runners. See
# add_sharded_test_pl_tests.
add_sharded_test_pl_tests(
  "${jbmc_strings_cmdline}" "core" ${jbmc_strings_shards} 1800)

# The symex-driven-lazy-loading run of this suite is the single largest CORE
# ctest on the macOS runners (~1-1.5h), and a single ctest test runs serially
# on one worker regardless of `ctest -jN`. Register it as several shards (see
# test.pl's --shard option) so the pieces run in parallel and the suite stops
# dominating the job's wall-clock.
add_sharded_test_pl_profile(
  "jbmc-strings-symex-driven-lazy-loading"
  "${jbmc_strings_cmdline} --symex-driven-lazy-loading"
  "-C;-X;symex-driven-lazy-loading-expected-failure"
  "CORE"
  "symex-driven-loading"
  ${jbmc_strings_shards}
  10800
)
