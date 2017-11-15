file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(java_bytecode ${sources})

generic_includes(java_bytecode)

target_link_libraries(java_bytecode util goto-programs miniz json)
