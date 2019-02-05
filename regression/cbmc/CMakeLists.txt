add_test_pl_tests(
    "$<TARGET_FILE:cbmc> --validate-goto-model" -X smt-backend
)

add_test_pl_profile(
    "cbmc-paths-lifo"
    "$<TARGET_FILE:cbmc> --paths lifo"
    "-C;-X;thorough-paths;-X;smt-backend;-s;paths-lifo"
    "CORE"
)
