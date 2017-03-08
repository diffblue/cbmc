file(GLOB_RECURSE sources "*.cpp")
add_library(analyses ${sources})

generic_includes(analyses)

target_link_libraries(analyses util goto-programs pointer-analysis)
