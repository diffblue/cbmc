if((NOT WIN32) AND (NOT APPLE) AND (NOT (CMAKE_SYSTEM_NAME STREQUAL "FreeBSD")))
add_test_pl_tests(
    "$<TARGET_FILE:cbmc> --validate-goto-model --validate-ssa-equation"
)
else()
add_test_pl_profile(
    "cbmc-concurrency"
    "$<TARGET_FILE:cbmc> --validate-goto-model --validate-ssa-equation"
    "-C;-X;pthread"
    "CORE"
)
endif()
