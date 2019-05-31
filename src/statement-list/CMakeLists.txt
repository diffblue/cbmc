generic_bison(statement_list)
generic_flex(statement_list)

file(GLOB_RECURSE sources "*.cpp" "*.h")

add_library(statement-list
    ${sources}
    ${BISON_parser_OUTPUTS}
    ${FLEX_scanner_OUTPUTS}
)

generic_includes(statement-list)

target_link_libraries(statement-list util)
