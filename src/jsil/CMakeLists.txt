generic_bison(jsil)
generic_flex(jsil)

file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(jsil
    ${sources}
    ${BISON_parser_OUTPUTS}
    ${FLEX_scanner_OUTPUTS}
)

generic_includes(jsil)

target_link_libraries(jsil util)
