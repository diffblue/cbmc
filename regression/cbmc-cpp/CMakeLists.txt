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
elseif(NOT CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  list(APPEND extra_excludes -X gcc-13)
endif()

add_test_pl_tests(
    "$<TARGET_FILE:cbmc> --validate-goto-model --validate-ssa-equation" ${gcc_only} ${extra_excludes} -X libcxx
)

# libc++ tests run without --validate-goto-model because system header
# processing may leave missing symbols in the goto model.
# Only enable if clang and libc++ headers are available.
find_program(CLANG_FOUND clang)
find_path(LIBCXX_FOUND "vector" PATHS /usr/include/c++/v1 /usr/lib/llvm-18/include/c++/v1 NO_DEFAULT_PATH)
if(CLANG_FOUND AND LIBCXX_FOUND)
  add_test_pl_profile(
      "cbmc-cpp-libcxx"
      "$<TARGET_FILE:cbmc>"
      -C CORE
      -I libcxx
      ${extra_excludes}
  )
endif()
