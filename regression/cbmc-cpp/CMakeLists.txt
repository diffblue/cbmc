if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC" OR
   NOT "${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
  set(gcc_only -X gcc-only)
else()
  set(gcc_only "")
endif()

# On GCC < 13, system header processing leaves more incomplete template
# symbols that cause --validate-goto-model to crash. Run validation
# only on GCC 13+ where headers are well-supported.
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU" AND
   CMAKE_CXX_COMPILER_VERSION VERSION_LESS "13")
  set(cbmc_cmd "$<TARGET_FILE:cbmc>")
else()
  set(cbmc_cmd "$<TARGET_FILE:cbmc> --validate-goto-model --validate-ssa-equation")
endif()

add_test_pl_tests(
    "${cbmc_cmd}" ${gcc_only} -X libcxx -X no-validate
)
set_tests_properties("cbmc-cpp-CORE" PROPERTIES TIMEOUT 1800)

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
      ${gcc_only}
  )
endif()
