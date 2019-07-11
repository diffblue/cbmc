generic_bison(rust)
generic_flex(rust)

file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(rust
    ${sources}
    ${BISON_parser_OUTPUTS}
    ${FLEX_scanner_OUTPUTS}
)

generic_includes(rust)

target_link_libraries(rust util)
