file(GLOB_RECURSE sources "*.cpp")
add_library(goto-symex ${sources})

generic_includes(goto-symex)

target_link_libraries(goto-symex util)
