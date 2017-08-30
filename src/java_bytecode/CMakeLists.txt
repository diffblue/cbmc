file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/java_bytecode_vtable.cpp
)
add_library(java_bytecode ${sources} ${headers})

generic_includes(java_bytecode)

target_link_libraries(java_bytecode util goto-programs miniz json)
