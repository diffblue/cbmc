if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
  set(gcc_only -X gcc-only)
  set(gcc_only_string "-X;gcc-only;")
else()
  set(gcc_only "")
  set(gcc_only_string "")
endif()

add_test_pl_tests(
    "$<TARGET_FILE:cbmc> --validate-goto-model --validate-ssa-equation" -X smt-backend ${gcc_only}
)

add_test_pl_profile(
    "cbmc-paths-lifo"
    "$<TARGET_FILE:cbmc> --paths lifo"
    "-C;-X;thorough-paths;-X;smt-backend;-X;paths-lifo-expected-failure;${gcc_only_string}-s;paths-lifo"
    "CORE"
)

add_test_pl_profile(
    "cbmc-cprover-smt2"
    "$<TARGET_FILE:cbmc> --cprover-smt2"
    "-C;-X;broken-smt-backend;-X;thorough-smt-backend;-X;broken-cprover-smt-backend;-X;thorough-cprover-smt-backend;${gcc_only_string}-s;cprover-smt2"
    "CORE"
)

# If `-I` (include flag) is passed, test.pl will run only the tests matching the label following it.
add_test_pl_profile(
  "cbmc-new-smt-backend"
  "$<TARGET_FILE:cbmc> --incremental-smt2-solver 'z3 --smt2 -in' --slice-formula"
  "-I;new-smt-backend;-s;new-smt-backend"
  "CORE"
)

# solver appears on the PATH in Windows already
if(NOT "${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
  set_property(
    TEST "cbmc-cprover-smt2-CORE"
    PROPERTY ENVIRONMENT
      "PATH=$ENV{PATH}:$<TARGET_FILE_DIR:smt2_solver>"
  )
endif()
