file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(langapi ${sources})

generic_includes(langapi)

target_link_libraries(langapi util)
