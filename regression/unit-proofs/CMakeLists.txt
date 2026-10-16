# Unit proofs: CBMC applied to its own code base with nondeterministic
# inputs (see README.md).  Only CORE entries run by default; KNOWNBUG
# entries track the front-end defect or scaling limit that blocks them.
# A `gcc-only' entry needs libstdc++ (not the MSVC STL or libc++; on the
# macOS CI job get_base_name timed out), and a `libstdcxx13' entry the
# libstdc++ headers of GCC >= 13 (cbmc preprocesses with the host gcc).
find_program(HOST_GCC gcc)
set(libstdcxx_exclusions "")
if(NOT "${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
  list(APPEND libstdcxx_exclusions -X gcc-only)
endif()
if(HOST_GCC)
  execute_process(
    COMMAND ${HOST_GCC} -dumpversion
    OUTPUT_VARIABLE HOST_GCC_VERSION
    OUTPUT_STRIP_TRAILING_WHITESPACE
    ERROR_QUIET)
  if(HOST_GCC_VERSION AND HOST_GCC_VERSION VERSION_LESS "13")
    list(APPEND libstdcxx_exclusions -X libstdcxx13)
  endif()
else()
  list(APPEND libstdcxx_exclusions -X libstdcxx13)
endif()
# A per-test timeout: the KNOWNBUG entries for scaling limits
# (edit_distance) do not terminate in reasonable time; under -K a [TIMEOUT]
# is the expected failure, instead of the whole profile's TIMEOUT.  The CORE
# proofs take under 20 s.
add_test_pl_tests(
    "$<TARGET_FILE:cbmc>" ${libstdcxx_exclusions} -t 300
)
set_tests_properties("unit-proofs-CORE" PROPERTIES TIMEOUT 900)
