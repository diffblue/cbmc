file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
add_library(analyses ${sources} ${headers})

generic_includes(analyses)

target_link_libraries(analyses util pointer-analysis)
