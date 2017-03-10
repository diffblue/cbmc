project(CBMC)

find_package(BISON)
find_package(FLEX)

find_package(Doxygen)
if(DOXYGEN_FOUND)
    add_custom_target(doc
        "${DOXYGEN_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/doxygen.cfg"
        WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
    )
endif(DOXYGEN_FOUND)

#   Add a bison target named 'parser'.
macro(generic_bison name)
    set(bison_header "${name}_y.tab.h")
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/${bison_header}")
        message(FATAL_ERROR "Generated file ${bison_header} found in source tree. If you previously built with `make`, run `make clean` and try again")
    endif()

    set(bison_source "${name}_y.tab.cpp")
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/${bison_source}")
        message(FATAL_ERROR "Generated file ${bison_source} found in source tree. If you previously built with `make`, run `make clean` and try again")
    endif()

    bison_target(
        parser
        "${CMAKE_CURRENT_SOURCE_DIR}/parser.y"
        "${CMAKE_CURRENT_BINARY_DIR}/${bison_source}"
        COMPILE_FLAGS "-pyy${name}"
    )
    set(renamed_parser_header "${CMAKE_CURRENT_BINARY_DIR}/${bison_header}")
    add_custom_command(OUTPUT "${renamed_parser_header}"
        COMMAND "${CMAKE_COMMAND}" -E copy "${BISON_parser_OUTPUT_HEADER}" "${renamed_parser_header}"
        MAIN_DEPENDENCY "${BISON_parser_OUTPUT_HEADER}"
    )
    list(REMOVE_ITEM BISON_parser_OUTPUTS "${BISON_parser_OUTPUT_HEADER}")
    list(APPEND BISON_parser_OUTPUTS "${renamed_parser_header}")
endmacro(generic_bison)

#   Add a flex target named 'scanner'
macro(generic_flex name)
    set(flex_source "${name}_lex.yy.cpp")
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/${flex_source}")
        message(FATAL_ERROR "Generated file ${flex_source} found in source tree. If you previously built with `make`, run `make clean` and try again")
    endif()

    flex_target(
        scanner
        "${CMAKE_CURRENT_SOURCE_DIR}/scanner.l"
        "${CMAKE_CURRENT_BINARY_DIR}/${name}_lex.yy.cpp"
        COMPILE_FLAGS "-Pyy${name}"
    )
endmacro(generic_flex)

#   Set the public include locations for a target.
macro(generic_includes name)
    target_include_directories(${name}
        PUBLIC
        ${CBMC_BINARY_DIR}
        ${CBMC_SOURCE_DIR}
        ${CMAKE_CURRENT_BINARY_DIR}
        ${CMAKE_CURRENT_SOURCE_DIR}
    )
endmacro(generic_includes)

#   Link optional modules.
#   Target is the name of the target with optional components.
#   Name is the name of the optional target.
#   Also adds a compile flag signalling to the preprocessor that the library is
#   used.
macro(add_if_library target name)
    if(TARGET ${name})
        target_link_libraries(${target} ${name})

        string(TOUPPER ${name} upper_name)
        string(REGEX REPLACE "-" "_" define ${upper_name})

        target_compile_definitions(${target} PUBLIC HAVE_${define})
    endif()
endmacro(add_if_library)

add_subdirectory(analyses)
add_subdirectory(ansi-c)
add_subdirectory(assembler)
add_subdirectory(big-int)
add_subdirectory(cpp)
add_subdirectory(goto-programs)
add_subdirectory(goto-symex)
add_subdirectory(jsil)
add_subdirectory(json)
add_subdirectory(json-symtab-language)
add_subdirectory(langapi)
add_subdirectory(linking)
add_subdirectory(pointer-analysis)
add_subdirectory(solvers)
add_subdirectory(util)
add_subdirectory(xmllang)

add_subdirectory(cbmc)
add_subdirectory(goto-cc)
add_subdirectory(goto-instrument)
add_subdirectory(goto-analyzer)
add_subdirectory(goto-diff)
