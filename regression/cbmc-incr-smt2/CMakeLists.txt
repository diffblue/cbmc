
if("${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
    set(exclude_win_broken_tests -X winbug)
else()
    set(exclude_win_broken_tests "")
endif()

add_test_pl_tests(
    "$<TARGET_FILE:cbmc> --validate-goto-model --validate-ssa-equation --slice-formula" ${exclude_win_broken_tests}
)
