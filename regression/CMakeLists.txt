set(test_pl_path "${CMAKE_CURRENT_SOURCE_DIR}/test.pl")

macro(add_test_pl_profile name cmdline flag profile)
    add_test(
        NAME "${name}-${profile}"
        COMMAND ${test_pl_path} -p -c ${cmdline} ${flag} ${ARGN}
        WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
    )
    set_tests_properties("${name}-${profile}" PROPERTIES
        LABELS "${profile};CBMC"
    )
endmacro(add_test_pl_profile)

macro(add_test_pl_tests cmdline)
    get_filename_component(TEST_DIR_NAME ${CMAKE_CURRENT_SOURCE_DIR} NAME)
    message(STATUS "Adding tests in directory: ${TEST_DIR_NAME}")
    add_test_pl_profile("${TEST_DIR_NAME}" "${cmdline}" -C CORE ${ARGN})
    add_test_pl_profile("${TEST_DIR_NAME}" "${cmdline}" -T THOROUGH ${ARGN})
    add_test_pl_profile("${TEST_DIR_NAME}" "${cmdline}" -F FUTURE ${ARGN})
    add_test_pl_profile("${TEST_DIR_NAME}" "${cmdline}" -K KNOWNBUG ${ARGN})
endmacro(add_test_pl_tests)

# For the best possible utilisation of multiple cores when
# running tests in parallel, it is important that these directories are
# listed with decreasing runtimes (i.e. longest running at the top)
add_subdirectory(cbmc)
add_subdirectory(cbmc-library)
add_subdirectory(goto-analyzer)
add_subdirectory(ansi-c)
add_subdirectory(goto-instrument)
add_subdirectory(cpp)
add_subdirectory(cbmc-cover)
add_subdirectory(goto-instrument-typedef)
add_subdirectory(smt2_solver)
add_subdirectory(strings)
add_subdirectory(invariants)
add_subdirectory(goto-diff)
add_subdirectory(test-script)
add_subdirectory(goto-analyzer-taint)
if(NOT WIN32)
  add_subdirectory(goto-gcc)
endif()
add_subdirectory(goto-cc-cbmc)
add_subdirectory(cbmc-cpp)
add_subdirectory(goto-cc-goto-analyzer)
add_subdirectory(systemc)
add_subdirectory(contracts)
