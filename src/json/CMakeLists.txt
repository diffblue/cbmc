generic_bison(json)
generic_flex(json)

file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
add_library(json 
    ${sources}
    ${headers}
    ${BISON_parser_OUTPUTS}
    ${FLEX_scanner_OUTPUTS}
)

generic_includes(json)

target_link_libraries(json util)
