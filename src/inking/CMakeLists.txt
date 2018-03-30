file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(inking ${sources})

generic_includes(inking)

target_link_libraries(inking util ansi-c)
