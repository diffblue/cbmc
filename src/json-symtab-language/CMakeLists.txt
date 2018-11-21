file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(json-symtab-language ${sources})

generic_includes(json-symtab-language)

target_link_libraries(json-symtab-language json util)
