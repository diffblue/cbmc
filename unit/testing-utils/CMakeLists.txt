file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(testing-utils ${sources})
target_link_libraries(testing-utils
    util
)
target_include_directories(testing-utils
    PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/..
)
