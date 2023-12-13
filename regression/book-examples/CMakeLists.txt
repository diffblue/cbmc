if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
  set(gcc_only -X gcc-only)
  set(gcc_only_string "-X;gcc-only;")
  set(exclude_win_broken_tests -X winbug)
  # We add the string at the end of the exclusion list, so it must not
  # have the `;` at the end or it bugs out.
  set(exclude_win_broken_tests_string "-X;winbug")
else()
  set(gcc_only "")
  set(gcc_only_string "")
  set(exclude_win_broken_tests "")
  set(exclude_win_broken_tests_string "")
endif()

add_test_pl_tests(
    "$<TARGET_FILE:cbmc> --no-standard-checks --validate-goto-model --validate-ssa-equation" -X smt-backend ${gcc_only} ${exclude_win_broken_tests}
)

add_test_pl_profile(
    "book-examples-paths-lifo"
    "$<TARGET_FILE:cbmc> --no-standard-checks --paths lifo"
    "-C;-X;thorough-paths;-X;smt-backend;-X;paths-lifo-expected-failure;${gcc_only_string}-s;paths-lifo;${exclude_win_broken_tests_string}"
    "CORE"
)

add_test_pl_profile(
    "book-examples-cprover-smt2"
    "$<TARGET_FILE:cbmc> --no-standard-checks --cprover-smt2"
    "-C;-X;broken-smt-backend;-X;thorough-smt-backend;-X;broken-cprover-smt-backend;-X;thorough-cprover-smt-backend;${gcc_only_string}-s;cprover-smt2;${exclude_win_broken_tests_string}"
    "CORE"
)

# If `-X` (exclude flag) is passed, test.pl will exclude the tests matching the label following it.
add_test_pl_profile(
  "book-examples-new-smt-backend"
  "$<TARGET_FILE:cbmc> --no-standard-checks --incremental-smt2-solver 'z3 --smt2 -in'"
  "${gcc_only_string}-X;no-new-smt;-s;new-smt-backend"
  "CORE"
)

# solver appears on the PATH in Windows already
if(NOT "${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
  set_property(
    TEST "book-examples-cprover-smt2-CORE"
    PROPERTY ENVIRONMENT
      "PATH=$ENV{PATH}:$<TARGET_FILE_DIR:smt2_solver>"
  )
endif()
