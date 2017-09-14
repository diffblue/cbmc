generic_flex(assembler)

file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
add_library(assembler
    ${sources}
    ${headers}
    ${FLEX_scanner_OUTPUTS}
)

generic_includes(assembler)

target_link_libraries(assembler util)
