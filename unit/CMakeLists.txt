if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang" OR
   "${CMAKE_CXX_COMPILER_ID}" STREQUAL "AppleClang" OR
   "${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU"
)
    #  private is overwritten in the gdb_api test cases
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-keyword-macro")
elseif("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
    #   This would be the place to enable warnings for Windows builds, although
    #   config.inc doesn't seem to do that currently
endif()

file(GLOB_RECURSE sources "*.cpp" "*.h")

file(GLOB_RECURSE testing_utils "testing-utils/*.cpp" "testing-utils/*.h")

if(NOT WITH_MEMORY_ANALYZER)
    file(GLOB_RECURSE memory_analyzer_sources "memory-analyzer/*.cpp")
    list(REMOVE_ITEM sources ${memory_analyzer_sources})
else()
    add_custom_command(OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/memory-analyzer"
        COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_CURRENT_BINARY_DIR}/memory-analyzer
    )
    function(make_mm_inc input output)
        add_custom_command(OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/memory-analyzer/${output}"
            COMMAND $<TARGET_FILE:file_converter>
                "${CMAKE_CURRENT_SOURCE_DIR}/memory-analyzer/${input}" >
                "${CMAKE_CURRENT_BINARY_DIR}/memory-analyzer/${output}"
            DEPENDS
              "${CMAKE_CURRENT_SOURCE_DIR}/memory-analyzer/${input}"
              "${CMAKE_CURRENT_BINARY_DIR}/memory-analyzer"
              $<TARGET_FILE:file_converter>
        )
    endfunction(make_mm_inc)

    make_mm_inc(input.txt input.inc)
    make_mm_inc(test.c test.inc)

    set(generated_mm_files
      "${CMAKE_CURRENT_BINARY_DIR}/memory-analyzer/input.inc"
      "${CMAKE_CURRENT_BINARY_DIR}/memory-analyzer/test.inc"
    )
    set_source_files_properties(
        "${CMAKE_CURRENT_SOURCE_DIR}/memory-analyzer/gdb_api.cpp"
        PROPERTIES
        OBJECT_DEPENDS "${generated_mm_files}"
    )
endif()

list(REMOVE_ITEM sources
    # Don't build
    ${CMAKE_CURRENT_SOURCE_DIR}/elf_reader.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/smt2_parser.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/json.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/cpp_parser.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/osx_fat_reader.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/wp.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/cpp_scanner.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/ieee_float.cpp

    # Will be built into a separate library and linked
    ${testing_utils}

    # Intended to fail to compile
    ${CMAKE_CURRENT_SOURCE_DIR}/util/expr_cast/expr_undefined_casts.cpp
)

add_subdirectory(testing-utils)

add_executable(unit ${sources})
target_include_directories(unit
    PUBLIC
    ${CBMC_BINARY_DIR}
    ${CBMC_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${CMAKE_CURRENT_BINARY_DIR}
    ${CUDD_INCLUDE}
)
target_link_libraries(
        unit
        testing-utils
        ansi-c
        solvers
        goto-cc-lib
        goto-checker
        goto-programs
        goto-instrument-lib
        goto-symex
        cbmc-lib
        json-symtab-language
        statement-list
)

add_test(
    NAME unit
    COMMAND $<TARGET_FILE:unit>
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
)

add_test(
    NAME unit-xfail
    COMMAND $<TARGET_FILE:unit> "[!shouldfail]"
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
)

set_tests_properties(unit PROPERTIES LABELS "CORE;CBMC")
