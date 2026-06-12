set(test_pl_path "${CMAKE_CURRENT_SOURCE_DIR}/test.pl")

macro(add_test_pl_profile name cmdline flag profile)
    add_test(
        NAME "${name}-${profile}"
        COMMAND perl ${test_pl_path} -e -p -c "${cmdline}" ${flag} ${ARGN}
        WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
    )
    set_tests_properties("${name}-${profile}" PROPERTIES
        LABELS "${profile};CBMC"
        TIMEOUT 1200
    )
    # Determine the log file name and register it for cmake clean.
    set(_test_pl_flags ${flag} ${ARGN})
    list(FIND _test_pl_flags "-s" _s_index)
    if(_s_index GREATER -1)
        math(EXPR _s_value_index "${_s_index} + 1")
        list(GET _test_pl_flags ${_s_value_index} _log_suffix)
        set_property(DIRECTORY "${CMAKE_SOURCE_DIR}" APPEND PROPERTY
            ADDITIONAL_CLEAN_FILES "${CMAKE_CURRENT_SOURCE_DIR}/tests-${_log_suffix}.log")
    else()
        set_property(DIRECTORY "${CMAKE_SOURCE_DIR}" APPEND PROPERTY
            ADDITIONAL_CLEAN_FILES "${CMAKE_CURRENT_SOURCE_DIR}/tests.log")
    endif()
endmacro(add_test_pl_profile)

# Register a test.pl profile split into <shard_count> shards (see test.pl's
# --shard option) so a long-running suite runs as several parallel ctest
# entries instead of one indivisible test. <base_flags> are the test.pl flags
# shared by all shards (excluding -s and --shard, which are appended per
# shard); each shard is named "<name>-<i>", logs to "<log_suffix>-<i>" and is
# given the supplied TIMEOUT.
function(add_sharded_test_pl_profile
         name cmdline base_flags profile log_suffix shard_count timeout)
    foreach(shard RANGE 1 ${shard_count})
        add_test_pl_profile(
            "${name}-${shard}"
            "${cmdline}"
            "${base_flags};--shard;${shard}/${shard_count};-s;${log_suffix}-${shard}"
            "${profile}"
        )
        set_tests_properties("${name}-${shard}-${profile}" PROPERTIES
            TIMEOUT ${timeout})
    endforeach()
endfunction(add_sharded_test_pl_profile)

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
add_subdirectory(cprover)
if(NOT WIN32)
  add_subdirectory(crangler)
endif()
add_subdirectory(goto-analyzer)
add_subdirectory(ansi-c)
add_subdirectory(goto-instrument)
add_subdirectory(cpp)
add_subdirectory(cbmc-concurrency)
add_subdirectory(cbmc-cover)
add_subdirectory(cbmc-incr-oneloop)
add_subdirectory(cbmc-incr-smt2)
add_subdirectory(cbmc-incr)
add_subdirectory(cbmc-shadow-memory)
add_subdirectory(cbmc-output-file)
add_subdirectory(cbmc-with-incr)
add_subdirectory(array-refinement-with-incr)
add_subdirectory(goto-instrument-chc)
add_subdirectory(goto-instrument-json)
add_subdirectory(goto-instrument-wmm-core)
add_subdirectory(goto-instrument-typedef)
add_subdirectory(goto-inspect)
add_subdirectory(smt2_solver)
add_subdirectory(smt2_strings)
add_subdirectory(strings)
add_subdirectory(invariants)
add_subdirectory(goto-diff)
add_subdirectory(test-script)
add_subdirectory(goto-analyzer-taint)
add_subdirectory(goto-bmc/goto-bmc-symex-ready-goto)
add_subdirectory(goto-bmc/goto-bmc-non-symex-ready-goto)
add_subdirectory(goto-bmc)
if(NOT WIN32)
  add_subdirectory(goto-gcc)
else()
  add_subdirectory(goto-cl)
endif()
add_subdirectory(goto-cc-cbmc)
add_subdirectory(cbmc-cpp)
add_subdirectory(goto-cc-goto-analyzer)
add_subdirectory(goto-analyzer-simplify)
add_subdirectory(statement-list)
add_subdirectory(systemc)
add_subdirectory(contracts)
add_subdirectory(contracts-dfcc)
add_subdirectory(goto-synthesizer)
add_subdirectory(acceleration)
add_subdirectory(k-induction)
add_subdirectory(goto-harness)
add_subdirectory(goto-harness-multi-file-project)
add_subdirectory(goto-cc-file-local)
if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
  add_subdirectory(cbmc-orphan-solver)
endif()
add_subdirectory(goto-cc-multi-file)
add_subdirectory(goto-cc-regression-gh-issue-5380)
add_subdirectory(linking-goto-binaries)
add_subdirectory(symtab2gb)
add_subdirectory(solver-hardness)
if(NOT WIN32)
  add_subdirectory(goto-ld)
endif()
add_subdirectory(validate-trace-xml-schema)
add_subdirectory(cbmc-primitives)
add_subdirectory(goto-interpreter)
add_subdirectory(cbmc-sequentialization)
add_subdirectory(cpp-linter)
add_subdirectory(catch-framework)
add_subdirectory(libcprover-cpp)
add_subdirectory(book-examples)

if(WITH_MEMORY_ANALYZER)
  add_subdirectory(snapshot-harness)
  add_subdirectory(memory-analyzer)
  add_subdirectory(extract_type_header)
endif()

