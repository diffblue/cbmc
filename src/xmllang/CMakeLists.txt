generic_bison(xml)
generic_flex(xml)

file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(xml
    ${sources}
    ${BISON_parser_OUTPUTS}
    ${FLEX_scanner_OUTPUTS}
)

generic_includes(xml)

target_link_libraries(xml util)
