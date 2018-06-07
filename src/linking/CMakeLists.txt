file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(linking ${sources})

generic_includes(linking)

target_link_libraries(linking util)
