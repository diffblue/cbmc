if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC" OR
   NOT "${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
  set(gcc_only -X gcc-only)
else()
  set(gcc_only "")
endif()

add_test_pl_tests(
    "$<TARGET_FILE:cbmc> --validate-goto-model --validate-ssa-equation" ${gcc_only}
)
