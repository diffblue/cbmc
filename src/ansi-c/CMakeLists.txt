generic_bison(ansi_c)
generic_flex(ansi_c)

add_executable(converter library/converter.cpp)

add_custom_command(OUTPUT converter_input.txt
    COMMAND cat ${CMAKE_CURRENT_SOURCE_DIR}/library/*.c > converter_input.txt
)

add_custom_command(OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/cprover_library.inc
    COMMAND converter < converter_input.txt > ${CMAKE_CURRENT_BINARY_DIR}/cprover_library.inc
    DEPENDS converter_input.txt
)

add_executable(file_converter file_converter.cpp)

function(make_inc name)
    add_custom_command(OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/${name}.inc
        COMMAND file_converter < ${CMAKE_CURRENT_SOURCE_DIR}/${name}.h > ${CMAKE_CURRENT_BINARY_DIR}/${name}.inc
    )
endfunction(make_inc)

make_inc(gcc_builtin_headers_generic)
make_inc(gcc_builtin_headers_ia32)
make_inc(gcc_builtin_headers_ia32-2)
make_inc(gcc_builtin_headers_alpha)
make_inc(gcc_builtin_headers_arm)
make_inc(gcc_builtin_headers_mips)
make_inc(gcc_builtin_headers_power)
make_inc(arm_builtin_headers)
make_inc(cw_builtin_headers)
make_inc(clang_builtin_headers)

file(GLOB_RECURSE sources "*.cpp")
add_library(ansi-c
    ${sources}
    ${BISON_parser_OUTPUTS}
    ${FLEX_scanner_OUTPUTS}
    ${CMAKE_CURRENT_BINARY_DIR}/cprover_library.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_generic.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_ia32.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_ia32-2.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_alpha.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_arm.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_mips.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_power.inc
    ${CMAKE_CURRENT_BINARY_DIR}/arm_builtin_headers.inc
    ${CMAKE_CURRENT_BINARY_DIR}/cw_builtin_headers.inc
    ${CMAKE_CURRENT_BINARY_DIR}/clang_builtin_headers.inc
)

generic_includes(ansi-c)

target_link_libraries(ansi-c util linking)
