if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
  set(gcc_only -X gcc-only)
else()
  set(gcc_only "")
endif()

set(extra_excludes "")
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU" AND CMAKE_CXX_COMPILER_VERSION VERSION_LESS "13")
  list(APPEND extra_excludes -X gcc-13)
elseif(NOT CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  list(APPEND extra_excludes -X gcc-13)
endif()

add_test_pl_tests(
    "$<TARGET_FILE:goto-cc>" ${gcc_only} ${extra_excludes}
)
