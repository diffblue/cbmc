set(extra_excludes "")
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU" AND CMAKE_CXX_COMPILER_VERSION VERSION_LESS "13")
  list(APPEND extra_excludes -X gcc-13)
elseif(NOT CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  list(APPEND extra_excludes -X gcc-13)
endif()

add_test_pl_tests(
    "$<TARGET_FILE:cbmc> --validate-goto-model --validate-ssa-equation" ${extra_excludes}
)
