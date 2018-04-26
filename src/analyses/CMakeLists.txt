file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/reaching_definitions.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/reaching_definitions_without_sharing.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/reaching_definitions_with_sharing.cpp
)
add_library(analyses ${sources})

generic_includes(analyses)

target_link_libraries(analyses util pointer-analysis)
