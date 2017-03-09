file(GLOB_RECURSE sources "*.cpp")
add_library(linking ${sources})

generic_includes(linking)

target_link_libraries(linking util ansi-c)
