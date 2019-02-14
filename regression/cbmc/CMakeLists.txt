add_test_pl_tests(
    "$<TARGET_FILE:cbmc> --validate-goto-model" -X smt-backend
)

add_test_pl_profile(
    "cbmc-paths-lifo"
    "$<TARGET_FILE:cbmc> --paths lifo"
    "-C;-X;thorough-paths;-X;smt-backend;-s;paths-lifo"
    "CORE"
)

add_test_pl_profile(
    "cbmc-cprover-smt2"
    "$<TARGET_FILE:cbmc> --cprover-smt2"
    "-C;-X;broken-smt-backend;-s;cprover-smt2"
    "CORE"
)
set_property(
  TEST "cbmc-cprover-smt2-CORE"
  PROPERTY ENVIRONMENT
    "PATH=$ENV{PATH}:${CMAKE_BINARY_DIR}/bin"
)
