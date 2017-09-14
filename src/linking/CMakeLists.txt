file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
add_library(linking ${sources} ${headers})

generic_includes(linking)

target_link_libraries(linking util ansi-c)
