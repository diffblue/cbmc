add_test_pl_tests(
    "$<TARGET_FILE:jbmc> --validate-goto-model --validate-ssa-equation --validate-trace"
)

# note: BDD_GUARDS is supplied as a C++ preprocessor flag (-DBDD_GUARDS via
# CMAKE_CXX_FLAGS, see COMPILING.md), not as a CMake variable, and nothing
# define()s it here. if(DEFINED BDD_GUARDS) is therefore effectively always
# false, so the else() branch (excluding bdd-expected-timeout) always wins.
# This preserves the pre-existing behaviour rather than implementing a working
# guards check; do not mistake it for one.
if(DEFINED BDD_GUARDS)
    set(symex_driven_exclude "-C;-X;symex-driven-lazy-loading-expected-failure")
else()
    set(symex_driven_exclude
        "-C;-X;symex-driven-lazy-loading-expected-failure;-X;bdd-expected-timeout")
endif()

# Shard the long-running symex-driven-lazy-loading run (see test.pl's --shard
# option) so it runs as several parallel ctest entries instead of one serial
# test.
add_sharded_test_pl_profile(
  "jbmc-symex-driven-lazy-loading"
  "$<TARGET_FILE:jbmc> --validate-goto-model --validate-ssa-equation --validate-trace --symex-driven-lazy-loading"
  "${symex_driven_exclude}"
  "CORE"
  "symex-driven-loading"
  3
  4800
)
