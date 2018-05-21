file(GLOB_RECURSE sources "*.cpp" "*.h")
list(APPEND sources  ${CBMC_SOURCE_DIR}/../unit/unit_tests.cpp)

file(GLOB_RECURSE java-testing_utils "java-testing-utils/*.cpp" "java-testing-utils/*.h")

list(REMOVE_ITEM sources
    # Don't build
    ${CMAKE_CURRENT_SOURCE_DIR}/sharing_map.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/elf_reader.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/smt2_parser.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/json.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/cpp_parser.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/osx_fat_reader.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/unicode.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/wp.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/cpp_scanner.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/float_utils.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/ieee_float.cpp

    # Will be built into a separate library and linked
    ${java-testing_utils}

    # Intended to fail to compile
    ${CMAKE_CURRENT_SOURCE_DIR}/util/expr_cast/expr_undefined_casts.cpp
)

add_subdirectory(java-testing-utils)

add_executable(java-unit ${sources})
target_include_directories(java-unit
    PUBLIC
    ${CBMC_BINARY_DIR}
    ${CBMC_SOURCE_DIR}
    ${CBMC_SOURCE_DIR}/../unit
    ${CMAKE_CURRENT_SOURCE_DIR}
)
target_link_libraries(java-unit
        java-testing-utils
        testing-utils
        ansi-c
        solvers
        goto-programs
        goto-instrument-lib
        cbmc-lib
)

add_test(
    NAME java-unit
    COMMAND $<TARGET_FILE:java-unit>
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
)
set_tests_properties(java-unit PROPERTIES LABELS "CORE;CBMC")
