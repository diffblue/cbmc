generic_bison(json)
generic_flex(json)

file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(json
    ${sources}
    ${BISON_parser_OUTPUTS}
    ${FLEX_scanner_OUTPUTS}
)

generic_includes(json)

target_link_libraries(json util)
