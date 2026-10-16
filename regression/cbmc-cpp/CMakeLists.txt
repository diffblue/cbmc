if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC" OR
   NOT "${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
  set(gcc_only -X gcc-only)
else()
  set(gcc_only "")
endif()

# Tests tagged `libstdcxxNN' need the libstdc++ headers of GCC >= NN (13:
# <format>): cbmc preprocesses with the HOST gcc (not necessarily the
# compiler cmake builds with), so ask it, and exclude the tags whose
# requirement it does not meet.
find_program(HOST_GCC gcc)
if(HOST_GCC)
  execute_process(
    COMMAND ${HOST_GCC} -dumpversion
    OUTPUT_VARIABLE HOST_GCC_VERSION
    OUTPUT_STRIP_TRAILING_WHITESPACE
    ERROR_QUIET)
  foreach(libstdcxx_version 12 13 16)
    if(HOST_GCC_VERSION AND
       HOST_GCC_VERSION VERSION_LESS "${libstdcxx_version}")
      list(APPEND gcc_only -X libstdcxx${libstdcxx_version})
    endif()
  endforeach()
  # `broken-libstdcxx16': known to fail with the libstdc++ 16 headers (a
  # temporary exclusion; each such test has a KNOWNBUG for its root cause)
  if(HOST_GCC_VERSION AND NOT HOST_GCC_VERSION VERSION_LESS "16")
    list(APPEND gcc_only -X broken-libstdcxx16)
  endif()
else()
  list(APPEND gcc_only -X libstdcxx12 -X libstdcxx13 -X libstdcxx16)
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

# A per-test timeout (-t) so that a single hanging test fails with
# [TIMEOUT] and its name instead of exhausting the whole suite's TIMEOUT
# (the slowest passing test took 339 s on the macOS CI runner).
set(cbmc_cpp_test_timeout -t 900)

add_test_pl_tests(
    "${cbmc_cmd}" ${gcc_only} -X libcxx ${cbmc_cpp_test_timeout}
)
set_tests_properties("cbmc-cpp-CORE" PROPERTIES TIMEOUT 4800)

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
      ${cbmc_cpp_test_timeout}
  )
  # ~15 minutes of libc++ header-heavy tests on the CI runners
  set_tests_properties("cbmc-cpp-libcxx-CORE" PROPERTIES TIMEOUT 2400)
endif()
