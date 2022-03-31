# On Windows, run only z3 tests
if("${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
    add_test_pl_profile(
        "cbmc-new-smt-backend-z3"
        "$<TARGET_FILE:cbmc> --incremental-smt2-solver 'z3 --smt2 -in' --validate-goto-model --validate-ssa-equation --slice-formula"
        "-C;X;winbug;-s;new-smt-z3"
        "CORE"
    )
else()
    # On Unix systems, run both z3 and cvc5
    add_test_pl_profile(
        "cbmc-new-smt-backend-z3"
        "$<TARGET_FILE:cbmc> --incremental-smt2-solver 'z3 --smt2 -in' --validate-goto-model --validate-ssa-equation --slice-formula"
        "-C;-s;new-smt-z3"
        "CORE"
    )

    add_test_pl_profile(
        "cbmc-new-smt-backend-cvc5"
        "$<TARGET_FILE:cbmc> --incremental-smt2-solver 'cvc5 --lang=smtlib2.6 --incremental' --validate-goto-model --validate-ssa-equation --slice-formula"
        "-C;-s;new-smt-cvc5"
        "CORE"
    )
endif()
