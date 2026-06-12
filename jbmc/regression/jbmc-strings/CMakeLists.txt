add_test_pl_tests(
    "$<TARGET_FILE:jbmc> --validate-goto-model --validate-ssa-equation"
)

# The symex-driven-lazy-loading run of this suite is the single largest CORE
# ctest on the macOS runners (~1-1.5h), and a single ctest test runs serially
# on one worker regardless of `ctest -jN`. Register it as several shards (see
# test.pl's --shard option) so the pieces run in parallel and the suite stops
# dominating the job's wall-clock.
add_sharded_test_pl_profile(
  "jbmc-strings-symex-driven-lazy-loading"
  "$<TARGET_FILE:jbmc> --validate-goto-model --validate-ssa-equation --symex-driven-lazy-loading"
  "-C;-X;symex-driven-lazy-loading-expected-failure"
  "CORE"
  "symex-driven-loading"
  4
  10800
)
set_tests_properties("jbmc-strings-CORE" PROPERTIES TIMEOUT 1800)
