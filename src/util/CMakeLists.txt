file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
add_library(util ${sources} ${headers})

generic_includes(util)

target_link_libraries(util big-int)
