file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(java-testing-utils ${sources})
target_link_libraries(java-testing-utils
    util
    java_bytecode
)
target_include_directories(java-testing-utils
    PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/..
    ${CBMC_SOURCE_DIR}/../unit
)
