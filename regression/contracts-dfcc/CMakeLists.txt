if(WIN32)
  set(is_windows true)
else()
  set(is_windows false)
endif()

if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
  set(gcc_only -X gcc-only)
  set(gcc_only_string "-X;gcc-only;")
else()
  set(gcc_only "")
  set(gcc_only_string "")
endif()


add_test_pl_tests(
    "${CMAKE_CURRENT_SOURCE_DIR}/chain.sh $<TARGET_FILE:goto-cc> $<TARGET_FILE:goto-instrument> $<TARGET_FILE:cbmc> ${is_windows}"
)

## Enabling these causes a very significant increase in the time taken to run the regressions

#add_test_pl_profile(
#    "cbmc-z3"
#    "${CMAKE_CURRENT_SOURCE_DIR}/chain.sh $<TARGET_FILE:goto-cc> $<TARGET_FILE:goto-instrument> '$<TARGET_FILE:cbmc> --z3' ${is_windows}"
#    "-C;-X;broken-smt-backend;-X;thorough-smt-backend;-X;broken-z3-backend;-X;thorough-z3-backend;${gcc_only_string}-s;z3"
#    "CORE"
#)

#add_test_pl_profile(
#    "cbmc-cprover-smt2"
#    "${CMAKE_CURRENT_SOURCE_DIR}/chain.sh $<TARGET_FILE:goto-cc> $<TARGET_FILE:goto-instrument> '$<TARGET_FILE:cbmc> --cprover-smt2' ${is_windows}"
#    "-C;-X;broken-smt-backend;-X;thorough-smt-backend;-X;broken-cprover-smt2-backend;-X;thorough-cprover-smt2-backend;${gcc_only_string}-s;cprover-smt2"
#    "CORE"
#)

# solver appears on the PATH in Windows already
#if(NOT "${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
#  set_property(
#    TEST "cbmc-cprover-smt2-CORE"
#    PROPERTY ENVIRONMENT
#      "PATH=$ENV{PATH}:$<TARGET_FILE_DIR:smt2_solver>"
#  )
#endif()
