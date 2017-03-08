file(GLOB_RECURSE sources "*.cpp")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/java_bytecode_vtable.cpp
)
add_library(java_bytecode ${sources})

generic_includes(java_bytecode)

target_link_libraries(java_bytecode util goto-programs)

if(TARGET zip)
    target_compile_definitions(java_bytecode PUBLIC HAVE_LIBZIP)
    target_link_libraries(java_bytecode zip)
endif()
