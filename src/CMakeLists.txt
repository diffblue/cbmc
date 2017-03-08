cmake_minimum_required(VERSION 3.2)

#   TODO
#   -[ ] Documentation target.
#   -[ ] Testing target.
#   -[ ] Automatically generate .class files from .java in java regression tests.
#   -[ ] Install profiles.
#   -[ ] Specify one of many different solver libraries.
#   -[x] Code signing.
#   -[x] Cprover jar build.

project(CBMC)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED true)

set(CMAKE_CXX_FLAGS ${CMAKE_CXX_FLAGS} -Wno-deprecated-register)

find_package(BISON)
find_package(FLEX)

set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

#   Add a bison target named 'parser'.
macro(generic_bison name)
    bison_target(
        parser
        ${CMAKE_CURRENT_SOURCE_DIR}/parser.y
        ${CMAKE_CURRENT_BINARY_DIR}/${name}_y.tab.cpp
        DEFINES_FILE ${CMAKE_CURRENT_BINARY_DIR}/${name}_y.tab.h
        COMPILE_FLAGS -pyy${name}
    )
endmacro(generic_bison)

#   Add a flex target named 'scanner'
macro(generic_flex name)
    flex_target(
        scanner
        ${CMAKE_CURRENT_SOURCE_DIR}/scanner.l
        ${CMAKE_CURRENT_BINARY_DIR}/${name}_lex.yy.cpp
        COMPILE_FLAGS -Pyy${name}
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

set(minisat_lib ${extern_location}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}minisat2-condensed${CMAKE_STATIC_LIBRARY_SUFFIX})

#   minisat download
#   This downloads minisat2, then patches it.
#   Then, it injects a minimal CMakeLists.txt so that we can build just the bits
#   we actually want, without having to update the provided makefile.
ExternalProject_Add(minisat2-extern
    PREFIX ${extern_location}
    URL http://ftp.debian.org/debian/pool/main/m/minisat2/minisat2_2.2.1.orig.tar.gz
    PATCH_COMMAND patch -p1 -i ${CMAKE_CURRENT_SOURCE_DIR}/../scripts/minisat-2.2.1-patch
          COMMAND cmake -E copy ${CMAKE_CURRENT_SOURCE_DIR}/../scripts/minisat2_CMakeLists.txt CMakeLists.txt
    CMAKE_ARGS -DCMAKE_INSTALL_PREFIX:PATH=<INSTALL_DIR>
    BUILD_BYPRODUCTS ${minisat_lib}
)

add_library(minisat2-condensed STATIC IMPORTED)
set_target_properties(minisat2-condensed PROPERTIES
    IMPORTED_LOCATION ${minisat_lib}
    INTERFACE_INCLUDE_DIRECTORIES "${extern_include_directory}"
)
add_dependencies(minisat2-condensed minisat2-extern)

#   Override add_executable to automatically sign the target on OSX.
function(add_executable name)
    _add_executable(${name} ${ARGN})
    set_target_properties(${name} PROPERTIES XCODE_ATTRIBUTE_CODE_SIGN_IDENTITY
        "Developer ID Application: Daniel Kroening")
endfunction(add_executable)

#   By default we don't add targets to ALL.
#   These still get built if other targets depend on them, though.
add_subdirectory(analyses EXCLUDE_FROM_ALL)
add_subdirectory(ansi-c EXCLUDE_FROM_ALL)
add_subdirectory(assembler EXCLUDE_FROM_ALL)
add_subdirectory(big-int EXCLUDE_FROM_ALL)
add_subdirectory(cpp EXCLUDE_FROM_ALL)
add_subdirectory(goto-programs EXCLUDE_FROM_ALL)
add_subdirectory(goto-symex EXCLUDE_FROM_ALL)
add_subdirectory(jsil EXCLUDE_FROM_ALL)
add_subdirectory(json EXCLUDE_FROM_ALL)
add_subdirectory(langapi EXCLUDE_FROM_ALL)
add_subdirectory(linking EXCLUDE_FROM_ALL)
add_subdirectory(memory-models EXCLUDE_FROM_ALL)
add_subdirectory(path-symex EXCLUDE_FROM_ALL)
add_subdirectory(pointer-analysis EXCLUDE_FROM_ALL)
add_subdirectory(solvers EXCLUDE_FROM_ALL)
add_subdirectory(util EXCLUDE_FROM_ALL)
add_subdirectory(xmllang EXCLUDE_FROM_ALL)
add_subdirectory(java_bytecode EXCLUDE_FROM_ALL)
add_subdirectory(cegis EXCLUDE_FROM_ALL)
add_subdirectory(miniz EXCLUDE_FROM_ALL)

#   Modules which depend on optional modules.
add_subdirectory(musketeer)
add_subdirectory(clobber)

#   These are the targets we want to build by default.
add_subdirectory(cbmc)
add_subdirectory(goto-cc)
add_subdirectory(goto-instrument)
add_subdirectory(symex)
add_subdirectory(goto-analyzer)
add_subdirectory(goto-diff)
