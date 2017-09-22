cmake_minimum_required(VERSION 3.2)

#   TODO
#   -[ ] Install profiles.
#   -[ ] Specify one of many different solver libraries.

project(CBMC)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED true)

set(CMAKE_EXPORT_COMPILE_COMMANDS true)

find_package(BISON)
find_package(FLEX)

set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

include(CPack)

find_package(Doxygen)
if(DOXYGEN_FOUND)
    add_custom_target(doc
        "${DOXYGEN_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/doxygen.cfg"
        WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
    )
endif(DOXYGEN_FOUND)

#   Add a bison target named 'parser'.
macro(generic_bison name)
    bison_target(
        parser
        "${CMAKE_CURRENT_SOURCE_DIR}/parser.y"
        "${CMAKE_CURRENT_BINARY_DIR}/${name}_y.tab.cpp"
        COMPILE_FLAGS "-pyy${name}"
    )
    set(renamed_parser_header "${CMAKE_CURRENT_BINARY_DIR}/${name}_y.tab.h")
    add_custom_command(OUTPUT "${renamed_parser_header}"
        COMMAND "${CMAKE_COMMAND}" -E copy "${BISON_parser_OUTPUT_HEADER}" "${renamed_parser_header}"
        MAIN_DEPENDENCY "${BISON_parser_OUTPUT_HEADER}"
    )
    list(REMOVE_ITEM BISON_parser_OUTPUTS "${BISON_parser_OUTPUT_HEADER}")
    list(APPEND BISON_parser_OUTPUTS "${renamed_parser_header}")
endmacro(generic_bison)

#   Add a flex target named 'scanner'
macro(generic_flex name)
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

#   EXTERNAL PROJECTS
include(ExternalProject)
set(extern_location ${CMAKE_CURRENT_BINARY_DIR}/extern)

set(extern_include_directory ${extern_location}/include)
file(MAKE_DIRECTORY ${extern_include_directory})

################################################################################

set(minisat_lib ${extern_location}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}minisat2-condensed${CMAKE_STATIC_LIBRARY_SUFFIX})

#   minisat download: This downloads minisat2, then patches it.  Then, it
#   injects a minimal CMakeLists.txt so that we can build just the bits we
#   actually want, without having to update the provided makefile.

ExternalProject_Add(minisat2-extern
    PREFIX ${extern_location}
    URL http://ftp.debian.org/debian/pool/main/m/minisat2/minisat2_2.2.1.orig.tar.gz
    PATCH_COMMAND patch -p1 -i ${CMAKE_CURRENT_SOURCE_DIR}/../scripts/minisat-2.2.1-patch
          COMMAND cmake -E copy ${CMAKE_CURRENT_SOURCE_DIR}/../scripts/minisat2_CMakeLists.txt CMakeLists.txt
          CMAKE_ARGS -DCMAKE_INSTALL_PREFIX:PATH=<INSTALL_DIR> -DCBMC_INCLUDE_DIR:path=${CMAKE_CURRENT_SOURCE_DIR}
    BUILD_BYPRODUCTS ${minisat_lib}
)

add_library(minisat2-condensed STATIC IMPORTED)
set_target_properties(minisat2-condensed PROPERTIES
    IMPORTED_LOCATION ${minisat_lib}
    INTERFACE_INCLUDE_DIRECTORIES "${extern_include_directory}"
)
add_dependencies(minisat2-condensed minisat2-extern)

################################################################################

set(glucose_lib ${extern_location}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}glucose-condensed${CMAKE_STATIC_LIBRARY_SUFFIX})

#   glucose download: This downloads glucose, then patches it.  Then, it
#   injects a minimal CMakeLists.txt so that we can build just the bits we
#   actually want, without having to update the provided makefile.

ExternalProject_Add(glucose-extern
    PREFIX ${extern_location}
    URL http://www.labri.fr/perso/lsimon/downloads/softwares/glucose-syrup.tgz
    PATCH_COMMAND patch -p1 -i ${CMAKE_CURRENT_SOURCE_DIR}/../scripts/glucose-syrup-patch
          COMMAND cmake -E copy ${CMAKE_CURRENT_SOURCE_DIR}/../scripts/glucose_CMakeLists.txt CMakeLists.txt
          CMAKE_ARGS -DCMAKE_INSTALL_PREFIX:PATH=<INSTALL_DIR>
    BUILD_BYPRODUCTS ${glucose_lib}
)

add_library(glucose-condensed STATIC IMPORTED)
set_target_properties(glucose-condensed PROPERTIES
    IMPORTED_LOCATION ${glucose_lib}
    INTERFACE_INCLUDE_DIRECTORIES "${extern_include_directory}"
)
add_dependencies(glucose-condensed glucose-extern)

################################################################################

#   Override add_executable to automatically sign the target on OSX.
function(add_executable name)
    _add_executable(${name} ${ARGN})
    set_target_properties(${name} PROPERTIES XCODE_ATTRIBUTE_CODE_SIGN_IDENTITY
        "Developer ID Application: Daniel Kroening")
endfunction(add_executable)

add_subdirectory(analyses)
add_subdirectory(ansi-c)
add_subdirectory(assembler)
add_subdirectory(big-int)
add_subdirectory(cpp)
add_subdirectory(goto-programs)
add_subdirectory(goto-symex)
add_subdirectory(jsil)
add_subdirectory(json)
add_subdirectory(langapi)
add_subdirectory(linking)
add_subdirectory(memory-models)
add_subdirectory(pointer-analysis)
add_subdirectory(solvers)
add_subdirectory(util)
add_subdirectory(xmllang)
add_subdirectory(java_bytecode)
add_subdirectory(miniz)
add_subdirectory(clobber)
add_subdirectory(cbmc)
add_subdirectory(goto-cc)
add_subdirectory(goto-instrument)
add_subdirectory(goto-analyzer)
add_subdirectory(goto-diff)
