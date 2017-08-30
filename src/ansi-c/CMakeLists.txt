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

################################################################################

if(MINGW)
    set(platform_unavail
        ${CMAKE_CURRENT_SOURCE_DIR}/library/java.io.c
        ${CMAKE_CURRENT_SOURCE_DIR}/library/err.c
        ${CMAKE_CURRENT_SOURCE_DIR}/library/threads.c
    )
else()
    set(platform_unavail
        ${CMAKE_CURRENT_SOURCE_DIR}/library/java.io.c
        ${CMAKE_CURRENT_SOURCE_DIR}/library/threads.c
    )
endif()

file(GLOB library_check_sources "library/*.c")
list(REMOVE_ITEM library_check_sources ${platform_unavail})

add_custom_target(library_check
    ${CMAKE_CURRENT_SOURCE_DIR}/check_library.sh ${library_check_sources}
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
)

################################################################################

make_inc(arm_builtin_headers)
make_inc(clang_builtin_headers)
make_inc(cw_builtin_headers)
make_inc(gcc_builtin_headers_alpha)
make_inc(gcc_builtin_headers_arm)
make_inc(gcc_builtin_headers_generic)
make_inc(gcc_builtin_headers_ia32)
make_inc(gcc_builtin_headers_ia32-2)
make_inc(gcc_builtin_headers_ia32-3)
make_inc(gcc_builtin_headers_ia32-4)
make_inc(gcc_builtin_headers_math)
make_inc(gcc_builtin_headers_mem_string)
make_inc(gcc_builtin_headers_mips)
make_inc(gcc_builtin_headers_omp)
make_inc(gcc_builtin_headers_power)
make_inc(gcc_builtin_headers_tm)
make_inc(gcc_builtin_headers_ubsan)

file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
add_library(ansi-c
    ${sources}
    ${headers}
    ${BISON_parser_OUTPUTS}
    ${FLEX_scanner_OUTPUTS}
    ${CMAKE_CURRENT_BINARY_DIR}/arm_builtin_headers.inc
    ${CMAKE_CURRENT_BINARY_DIR}/clang_builtin_headers.inc
    ${CMAKE_CURRENT_BINARY_DIR}/cprover_library.inc
    ${CMAKE_CURRENT_BINARY_DIR}/cw_builtin_headers.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_alpha.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_arm.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_generic.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_ia32-2.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_ia32-3.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_ia32-4.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_ia32.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_math.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_mem_string.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_mips.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_omp.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_power.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_tm.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_ubsan.inc
)

generic_includes(ansi-c)

target_link_libraries(ansi-c util linking goto-programs assembler)
