file(GLOB_RECURSE sources "*.cpp" "*.h")

file(GLOB_RECURSE testing_utils "testing-utils/*.cpp" "testing-utils/*.h")

list(REMOVE_ITEM sources
    # Don't build
    ${CMAKE_CURRENT_SOURCE_DIR}/elf_reader.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/smt2_parser.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/json.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/cpp_parser.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/osx_fat_reader.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/wp.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/cpp_scanner.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/ieee_float.cpp

    # Will be built into a separate library and linked
    ${testing_utils}

    # Has additional dependencies, needs to be built as a separate lib
    ${CMAKE_CURRENT_SOURCE_DIR}/dispatch-loop-detector/dispatch_loop_detector.cpp

    # Intended to fail to compile
    ${CMAKE_CURRENT_SOURCE_DIR}/util/expr_cast/expr_undefined_casts.cpp
)

add_subdirectory(testing-utils)
add_subdirectory(dispatch-loop-detector)

add_executable(unit ${sources})

target_include_directories(unit
    PUBLIC
    ${CBMC_BINARY_DIR}
    ${CBMC_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}
)
target_link_libraries(
        unit
        testing-utils
        dispatch-loop-detector
        ansi-c
        solvers
        goto-programs
        goto-instrument-lib
        cbmc-lib
)

add_test(
    NAME unit
    COMMAND $<TARGET_FILE:unit>
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
)
set_tests_properties(unit PROPERTIES LABELS "CORE;CBMC")
