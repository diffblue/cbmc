generic_bison(ansi_c)
generic_flex(ansi_c)

add_executable(converter library/converter.cpp)

file(GLOB ansi_c_library_sources "library/*.c")

add_custom_command(OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/cprover_library.inc"
    COMMAND $<TARGET_FILE:converter> ${ansi_c_library_sources} > "${CMAKE_CURRENT_BINARY_DIR}/cprover_library.inc"
    DEPENDS converter ${ansi_c_library_sources})

add_executable(file_converter file_converter.cpp)

function(make_inc name)
    add_custom_command(OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/${name}.inc"
        COMMAND file_converter "${CMAKE_CURRENT_SOURCE_DIR}/${name}.h" > "${CMAKE_CURRENT_BINARY_DIR}/${name}.inc"
        DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/${name}.h" file_converter
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

add_custom_command(
    DEPENDS ${library_check_sources}
    COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/library_check.sh ${CMAKE_C_COMPILER} ${library_check_sources}
    COMMAND ${CMAKE_COMMAND} -E touch ${CMAKE_CURRENT_BINARY_DIR}/library-check.stamp
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/library-check.stamp
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
)

if(NOT "${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
    add_custom_target(c_library_check
        DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/library-check.stamp
)
endif()

################################################################################

make_inc(arm_builtin_headers)
make_inc(clang_builtin_headers)
make_inc(cprover_builtin_headers)
make_inc(cw_builtin_headers)
make_inc(gcc_builtin_headers_alpha)
make_inc(gcc_builtin_headers_arm)
make_inc(gcc_builtin_headers_generic)
make_inc(gcc_builtin_headers_ia32)
make_inc(gcc_builtin_headers_ia32-2)
make_inc(gcc_builtin_headers_ia32-3)
make_inc(gcc_builtin_headers_ia32-4)
make_inc(gcc_builtin_headers_ia32-5)
make_inc(gcc_builtin_headers_math)
make_inc(gcc_builtin_headers_mem_string)
make_inc(gcc_builtin_headers_mips)
make_inc(gcc_builtin_headers_omp)
make_inc(gcc_builtin_headers_power)
make_inc(gcc_builtin_headers_tm)
make_inc(gcc_builtin_headers_types)
make_inc(gcc_builtin_headers_ubsan)
make_inc(windows_builtin_headers)

set(extra_dependencies
    ${CMAKE_CURRENT_BINARY_DIR}/arm_builtin_headers.inc
    ${CMAKE_CURRENT_BINARY_DIR}/clang_builtin_headers.inc
    ${CMAKE_CURRENT_BINARY_DIR}/cprover_library.inc
    ${CMAKE_CURRENT_BINARY_DIR}/cprover_builtin_headers.inc
    ${CMAKE_CURRENT_BINARY_DIR}/cw_builtin_headers.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_alpha.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_arm.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_generic.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_ia32-2.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_ia32-3.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_ia32-4.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_ia32-5.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_ia32.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_math.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_mem_string.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_mips.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_omp.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_power.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_tm.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_types.inc
    ${CMAKE_CURRENT_BINARY_DIR}/gcc_builtin_headers_ubsan.inc
    ${CMAKE_CURRENT_BINARY_DIR}/windows_builtin_headers.inc
    ${CMAKE_CURRENT_BINARY_DIR}/library-check.stamp
)

if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
    list(REMOVE_ITEM
         extra_dependencies
         ${CMAKE_CURRENT_BINARY_DIR}/library-check.stamp)
endif()

file(GLOB_RECURSE sources "*.cpp" "*.h")

list(REMOVE_ITEM sources
    "${CMAKE_CURRENT_SOURCE_DIR}/library/converter.cpp"
    "${CMAKE_CURRENT_SOURCE_DIR}/file_converter.cpp"
)

add_library(ansi-c
    ${sources}
    ${BISON_parser_OUTPUTS}
    ${FLEX_scanner_OUTPUTS}
)

set_source_files_properties(
    ${sources}
    PROPERTIES
    OBJECT_DEPENDS "${extra_dependencies}"
)

generic_includes(ansi-c)

target_link_libraries(ansi-c util linking goto-programs assembler)
