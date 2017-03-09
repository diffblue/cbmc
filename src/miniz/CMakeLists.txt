file(GLOB_RECURSE sources "*.cpp")
add_library(miniz ${sources})

generic_includes(miniz)

target_link_libraries(miniz)
