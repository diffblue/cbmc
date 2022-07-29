find_program(Z3_EXISTS "z3")
message(${Z3_EXISTS})
if(Z3_EXISTS)
    add_test_pl_tests(
        "$<TARGET_FILE:cbmc>"
    )

    # If `-I` (include flag) is passed, test.pl will run only the tests matching the label following it.
    add_test_pl_profile(
            "cbmc-new-smt-backend"
            "$<TARGET_FILE:cbmc> --incremental-smt2-solver 'z3 --smt2 -in' --slice-formula"
            "-I;new-smt-backend;-s;new-smt-backend"
            "CORE"
    )
else()
    add_test_pl_tests(
        "$<TARGET_FILE:cbmc>" -X smt-backend
    )
endif()
