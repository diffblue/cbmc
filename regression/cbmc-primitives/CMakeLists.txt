find_program(Z3_EXISTS "z3")
message(${Z3_EXISTS})
if(Z3_EXISTS)
    add_test_pl_tests(
        "$<TARGET_FILE:cbmc>"
    )
else()
    add_test_pl_tests(
        "$<TARGET_FILE:cbmc>" -X smt-backend
    )
endif()
