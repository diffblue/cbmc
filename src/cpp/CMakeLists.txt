file(GLOB cpp_library_sources "library/*.c")

add_custom_command(OUTPUT converter_input.txt
    COMMAND cat ${cpp_library_sources} > converter_input.txt
    DEPENDS ${cpp_library_sources}
)

add_custom_command(OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/cprover_library.inc"
    COMMAND ../ansi-c/converter < "converter_input.txt" > "${CMAKE_CURRENT_BINARY_DIR}/cprover_library.inc"
    DEPENDS "converter_input.txt" ../ansi-c/converter
)

################################################################################

file(GLOB library_check_sources "library/*.c")

add_custom_command(
    DEPENDS ${library_check_sources}
    COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../ansi-c/library_check.sh ${CMAKE_C_COMPILER} ${library_check_sources}
    COMMAND ${CMAKE_COMMAND} -E touch ${CMAKE_CURRENT_BINARY_DIR}/library-check.stamp
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/library-check.stamp
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
)

if(NOT "${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
    add_custom_target(cpp_library_check
        DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/library-check.stamp
)
endif()

################################################################################

file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(cpp ${sources})

generic_includes(cpp)

target_link_libraries(cpp util ansi-c)
