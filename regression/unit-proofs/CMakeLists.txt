# Unit proofs: CBMC applied to its own code base with nondeterministic
# inputs (see README.md).  Only CORE entries run by default; KNOWNBUG
# entries track the front-end defect or scaling limit that blocks them.
# A `libstdcxx13' entry needs the libstdc++ headers of GCC >= 13 (cbmc
# preprocesses with the host gcc).
find_program(HOST_GCC gcc)
set(libstdcxx_exclusions "")
if(HOST_GCC)
  execute_process(
    COMMAND ${HOST_GCC} -dumpversion
    OUTPUT_VARIABLE HOST_GCC_VERSION
    OUTPUT_STRIP_TRAILING_WHITESPACE
    ERROR_QUIET)
  if(HOST_GCC_VERSION AND HOST_GCC_VERSION VERSION_LESS "13")
    set(libstdcxx_exclusions -X libstdcxx13)
  endif()
else()
  set(libstdcxx_exclusions -X libstdcxx13)
endif()
add_test_pl_tests(
    "$<TARGET_FILE:cbmc>" ${libstdcxx_exclusions}
)
set_tests_properties("unit-proofs-CORE" PROPERTIES TIMEOUT 900)
