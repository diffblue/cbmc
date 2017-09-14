file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
add_library(langapi ${sources} ${headers})

generic_includes(langapi)

target_link_libraries(langapi util)
