# `goto-bmc` is supposed to operate only on symex-ready goto binary files, so
# we follow two different paths to make sure that it's behaviour is correct:

# First suite of tests is supposed to be tests against symex-ready goto. For these,
# goto-bmc is capable of handling those, and so we produce them using
# `cbmc --export-symex-ready-goto <file>`.
add_test_pl_tests(
    "${CMAKE_CURRENT_SOURCE_DIR}/chain.sh $<TARGET_FILE:cbmc> $<TARGET_FILE:goto-bmc>"
)

# Second suite of tests is in folder `regression/goto-bmc-non-symex-ready-goto/`
