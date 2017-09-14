generic_bison(jsil)
generic_flex(jsil)

file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
add_library(jsil
    ${sources}
    ${headers}
    ${BISON_parser_OUTPUTS}
    ${FLEX_scanner_OUTPUTS}
)

generic_includes(jsil)

target_link_libraries(jsil util)
