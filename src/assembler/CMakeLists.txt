generic_flex(assembler)

file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(assembler
    ${sources}
    ${FLEX_scanner_OUTPUTS}
)

generic_includes(assembler)

target_link_libraries(assembler util)
