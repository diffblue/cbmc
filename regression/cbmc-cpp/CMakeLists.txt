if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
  set(gcc_only -X gcc-only)
else()
  set(gcc_only "")
endif()

# Tests tagged 'gcc-13' require GCC 13+ libstdc++ headers
# Tests tagged 'libcxx' require clang and libc++ (installed on Ubuntu CI)
set(extra_excludes "")
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU" AND CMAKE_CXX_COMPILER_VERSION VERSION_LESS "13")
  list(APPEND extra_excludes -X gcc-13)
elseif(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
  list(APPEND extra_excludes -X gcc-13)
elseif(CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
  list(APPEND extra_excludes -X libcxx)
endif()

add_test_pl_tests(
    "$<TARGET_FILE:cbmc> --validate-goto-model --validate-ssa-equation" ${gcc_only} ${extra_excludes}
)
