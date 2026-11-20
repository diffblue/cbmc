if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
  set(gcc_only_string "-X;gcc-only;")
else()
  set(gcc_only_string "")
endif()

if((NOT WIN32) AND (NOT APPLE) AND (NOT (CMAKE_SYSTEM_NAME STREQUAL "FreeBSD")))
add_test_pl_tests(
    "$<TARGET_FILE:cbmc> --validate-goto-model --validate-ssa-equation"
)
else()
add_test_pl_profile(
    "cbmc-concurrency"
    "$<TARGET_FILE:cbmc> --validate-goto-model --validate-ssa-equation"
    "${gcc_only_string}-C;-X;pthread"
    "CORE"
)
endif()
