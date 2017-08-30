file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/goto_convert_new_switch_case.cpp
)
add_library(goto-programs ${sources} ${headers})

generic_includes(goto-programs)

target_link_libraries(goto-programs util assembler langapi analyses ansi-c)
