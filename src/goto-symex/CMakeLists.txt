file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
add_library(goto-symex ${sources} ${headers})

generic_includes(goto-symex)

target_link_libraries(goto-symex util)
