file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(goto-checker ${sources})

generic_includes(goto-checker)

target_link_libraries(goto-checker goto-programs goto-symex solvers util)
