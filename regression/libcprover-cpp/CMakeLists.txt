file(GLOB_RECURSE api_sources "../src/libcprover-cpp/*.cpp" "../src/libcprover-cpp/*.h")

# This step builds a binary driving the API (to be used for testing)
add_executable(api-binary-driver call_bmc.cpp ${api_sources})
cprover_default_properties(api-binary-driver)
target_include_directories(api-binary-driver
    PUBLIC
    ${CBMC_BINARY_DIR}
    ${CBMC_SOURCE_DIR}
    # TODO: Should be fixed for the proper include form.
    ${CMAKE_CURRENT_SOURCE_DIR}/../src/libcprover-cpp/)
target_link_libraries(api-binary-driver goto-programs util langapi ansi-c cprover-api-cpp)

# Enable test running
set(test_pl_path "${CBMC_SOURCE_DIR}/../regression/test.pl")

macro(add_test_pl_profile name cmdline flag profile)
    add_test(
        NAME "${name}-${profile}"
        COMMAND perl ${test_pl_path} -e -p -c "${cmdline}" ${flag} ${ARGN}
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
add_subdirectory(model_loading)
