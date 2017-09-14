file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
add_library(goto-programs ${sources} ${headers})

generic_includes(goto-programs)

target_link_libraries(goto-programs util assembler langapi analyses ansi-c)
