file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
add_library(miniz ${sources} ${headers})

generic_includes(miniz)

target_link_libraries(miniz)
