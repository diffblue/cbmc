add_test_pl_tests(
    "$<TARGET_FILE:jbmc> --validate-goto-model --validate-ssa-equation"
)

# Shard the long-running symex-driven-lazy-loading run (see test.pl's --shard
# option) so it runs as several parallel ctest entries instead of one serial
# test.
add_sharded_test_pl_profile(
  "strings-smoke-tests-symex-driven-lazy-loading"
  "$<TARGET_FILE:jbmc> --validate-goto-model --validate-ssa-equation --symex-driven-lazy-loading"
  "-C;-X;symex-driven-lazy-loading-expected-failure"
  "CORE"
  "symex-driven-loading"
  2
  1800
)
