add_test_pl_tests(
    "$<TARGET_FILE:cbmc> --validate-goto-model" -X smt-backend
)
