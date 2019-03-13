file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(goto-symex ${sources} single_value_set_dereference_callback.h single_value_set_dereference_callback.cpp)

generic_includes(goto-symex)

target_link_libraries(goto-symex util)
