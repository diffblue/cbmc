file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(goto-checker ${sources})

generic_includes(goto-checker)

find_package(Threads REQUIRED)
target_link_libraries(
  goto-checker goto-programs goto-symex solvers util xml Threads::Threads
)
