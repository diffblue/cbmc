
file(GLOB_RECURSE sources "*.cpp" "*.h")

add_executable(lib-unit ${sources})
target_include_directories(lib-unit
    PUBLIC
    ${CBMC_SOURCE_DIR}/libcprover-cpp
)
target_link_libraries(lib-unit
    cprover-api-cpp
)

add_test(
    NAME lib-unit
    COMMAND $<TARGET_FILE:lib-unit>
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
)

set_tests_properties(lib-unit PROPERTIES LABELS "CORE;CBMC")
