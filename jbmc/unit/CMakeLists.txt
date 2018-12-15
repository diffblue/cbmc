file(GLOB_RECURSE sources "*.cpp" "*.h")
list(APPEND sources  ${CBMC_SOURCE_DIR}/../unit/unit_tests.cpp)

file(GLOB_RECURSE java-testing_utils "java-testing-utils/*.cpp" "java-testing-utils/*.h")

list(REMOVE_ITEM sources
    # Will be built into a separate library and linked
    ${java-testing_utils}
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
        goto-checker
        goto-programs
        goto-symex
        goto-instrument-lib
        cbmc-lib
        json-symtab-language
)

add_test(
    NAME java-unit
    COMMAND $<TARGET_FILE:java-unit>
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
)
set_tests_properties(java-unit PROPERTIES LABELS "CORE;CBMC")
