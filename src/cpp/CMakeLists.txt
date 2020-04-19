file(GLOB cpp_library_sources "library/*.c")

# Convert cmake paths to native paths for Windows builds
file(TO_NATIVE_PATH "${cpp_library_sources}"
     cpp_library_sources_paths)
file(TO_NATIVE_PATH "${CMAKE_CURRENT_BINARY_DIR}/cprover_library.inc"
     cprover_library_path)
file(TO_NATIVE_PATH "${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/converter"
     converter_path)

add_custom_command(OUTPUT "${cprover_library_path}"
        COMMAND cat ${cpp_library_sources_paths} | "${converter_path}" > "${cprover_library_path}"
        DEPENDS converter ${cpp_library_sources_paths})

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

set_source_files_properties(
        ${sources}
        PROPERTIES
        OBJECT_DEPENDS "${CMAKE_CURRENT_BINARY_DIR}/cprover_library.inc"
)

generic_includes(cpp)

target_link_libraries(cpp util ansi-c)
