file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
add_library(path-symex ${sources} ${headers})

generic_includes(path-symex)

target_link_libraries(path-symex util pointer-analysis)
