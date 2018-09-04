cmake_minimum_required(VERSION 3.2)

find_program(CCACHE_PROGRAM ccache)
if(CCACHE_PROGRAM)
    set_property(GLOBAL PROPERTY RULE_LAUNCH_COMPILE "${CCACHE_PROGRAM}")
    message(STATUS "Rule launch compile: ${CCACHE_PROGRAM}")
 endif()

set(CMAKE_EXPORT_COMPILE_COMMANDS true)

set(CMAKE_OSX_DEPLOYMENT_TARGET 10.9)

include(GNUInstallDirs)

set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang" OR
   "${CMAKE_CXX_COMPILER_ID}" STREQUAL "AppleClang" OR
   "${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU"
)
    #   Ensure NDEBUG is not set for release builds
    set(CMAKE_CXX_FLAGS_RELEASE "-O2")
    #   Enable lots of warnings
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wpedantic -Werror -Wno-deprecated-declarations")
elseif("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
    #   This would be the place to enable warnings for Windows builds, although
    #   config.inc doesn't seem to do that currently
endif()

set(enable_cbmc_tests on CACHE BOOL "Whether CBMC tests should be enabled")

set(sat_impl "minisat2" CACHE STRING
    "This setting controls the SAT library which is used. Valid values are 'minisat2' and 'glucose'"
)

if(${enable_cbmc_tests})
    enable_testing()
endif()

add_subdirectory(src)
add_subdirectory(regression)
add_subdirectory(unit)

add_subdirectory(jbmc)

set_target_properties(
    analyses
    ansi-c
    assembler
    big-int
    cbmc
    cbmc-lib
    cpp
    driver
    goto-analyzer
    goto-analyzer-lib
    goto-cc
    goto-cc-lib
    goto-diff
    goto-diff-lib
    goto-instrument
    goto-instrument-lib
    goto-programs
    goto-symex
    jsil
    json
    langapi
    linking
    pointer-analysis
    solvers
    testing-utils
    unit
    util
    xml

    java_bytecode
    java-models-library
    jbmc
    jbmc-lib
    janalyzer
    janalyzer-lib
    jdiff
    jdiff-lib
    java-testing-utils
    java-unit
    miniz

    PROPERTIES
    CXX_STANDARD 11
    CXX_STANDARD_REQUIRED true
    XCODE_ATTRIBUTE_CODE_SIGN_IDENTITY "Developer ID Application: Daniel Kroening"
)
