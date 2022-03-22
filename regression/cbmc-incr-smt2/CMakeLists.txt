
if("${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
    set(exclude_win_broken_tests -X winbug)
else()
    set(exclude_win_broken_tests "")
endif()

add_test_pl_profile(
    "cbmc-new-smt-backend-z3"
    "$<TARGET_FILE:cbmc> --incremental-smt2-solver 'z3 --smt2 -in' --validate-goto-model --validate-ssa-equation --slice-formula ${exclude_win_broken_tests}"
    "-C;-s;new-smt-z3"
    "CORE"
)

add_test_pl_profile(
    "cbmc-new-smt-backend-cvc5"
    "$<TARGET_FILE:cbmc> --incremental-smt2-solver 'cvc5 --lang smt --incremental' --validate-goto-model --validate-ssa-equation --slice-formula ${exclude_win_broken_tests}"
    "-C;-s;new-smt-cvc5"
    "CORE"
)
