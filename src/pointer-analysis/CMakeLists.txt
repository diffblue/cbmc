file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
add_library(pointer-analysis ${sources} ${headers})

generic_includes(pointer-analysis)

target_link_libraries(pointer-analysis util analyses goto-programs)
