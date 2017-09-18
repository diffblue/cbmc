set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED true)

set(test_pl_path "${CMAKE_CURRENT_SOURCE_DIR}/test.pl")

macro(add_test_pl_profile name cmdline flag profile)
    add_test(
        NAME "${name}-${profile}"
        COMMAND ${test_pl_path} -c ${cmdline} ${flag}
        WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
    )
    set_tests_properties("${name}-${profile}" PROPERTIES
        LABELS "${profile}"
    )
endmacro(add_test_pl_profile)

macro(add_test_pl_tests name cmdline)
    add_test_pl_profile("${name}" "${cmdline}" -C CORE)
    add_test_pl_profile("${name}" "${cmdline}" -T THOROUGH)
    add_test_pl_profile("${name}" "${cmdline}" -F FUTURE)
    add_test_pl_profile("${name}" "${cmdline}" -K KNOWNBUG)
endmacro(add_test_pl_tests)

add_subdirectory(ansi-c)
add_subdirectory(cbmc)
add_subdirectory(cbmc-java)
add_subdirectory(cbmc-java-inheritance)
add_subdirectory(cpp)
add_subdirectory(goto-analyzer)
add_subdirectory(goto-cc-cbmc)
add_subdirectory(goto-cc-goto-analyzer)
add_subdirectory(goto-diff)
add_subdirectory(goto-instrument)
add_subdirectory(goto-instrument-typedef)
add_subdirectory(invariants)
add_subdirectory(strings)
add_subdirectory(strings-smoke-tests)
add_subdirectory(test-script)
