generic_bison(mm)
generic_flex(mm)

file(GLOB_RECURSE sources "*.cpp")
add_library(mmcc
    ${sources}
    ${BISON_parser_OUTPUTS}
    ${FLEX_scanner_OUTPUTS}
)

generic_includes(mmcc)

target_link_libraries(mmcc util)
