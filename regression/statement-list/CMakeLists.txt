add_test_pl_tests(
    "$<TARGET_FILE:cbmc>" -X smt-backend
)
