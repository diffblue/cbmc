if("${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
    set(is_windows true)
else()
    set(is_windows false)
endif()

# Second suite of tests is running `goto-cc` to produce "normal" goto-binaries,
# which we expect `goto-bmc` to reject in some capacity. For now, it just fails
# non-gracefully, with invariant violations. This behaviour is important enough
# that we want to test for it, but we expect the software to become better behaved
# in the future (by checking that the input binary *is* in symex-ready-goto form
# and if not produce appropriate error reporting for the user).
add_test_pl_tests(
    "${CMAKE_CURRENT_SOURCE_DIR}/chain.sh $<TARGET_FILE:goto-cc> $<TARGET_FILE:goto-bmc> ${is_windows}"
)
