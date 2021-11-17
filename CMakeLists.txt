cmake_minimum_required(VERSION 3.2)

# Compile with /usr/bin/clang on MacOS
# See https://github.com/diffblue/cbmc/issues/4956
#
if (CMAKE_HOST_SYSTEM_NAME STREQUAL Darwin)
    if(NOT DEFINED CMAKE_C_COMPILER)
        message(STATUS "Setting CMAKE_C_COMPILER to /usr/bin/clang for MacOS")
        set(CMAKE_C_COMPILER "/usr/bin/clang")
    endif()
endif()

# If cmake generates files inside of the cbmc source directory this can lead to important files being overwritten, so we prevent that here
if("${CMAKE_BINARY_DIR}" STREQUAL "${CMAKE_SOURCE_DIR}")
  message(FATAL_ERROR
    "We have detected that you were trying to invoke cmake with its output"
    " directory being equal to the source directory.  You may have done this by"
    " accident by invoking cmake from the cbmc top level directory without"
    " specifying a build directory.  Since this can lead to cmake overwriting"
    " files in the source tree, this is prohibited.  Please perform an"
    " out-of-source build by either creating a separate build directory and"
    " invoking cmake from there, or specifying a build directory with -B.\n"
    "(see also: COMPILING.md)\n"
    "Note that running this command will have created CMakeCache.txt"
    " and a CMakeFiles directory; You should delete both of them.")
endif()

# Build a Release version by default (default build flags for each build type
# are configured below).
if (NOT EXISTS ${CMAKE_BINARY_DIR}/CMakeCache.txt)
    if (NOT CMAKE_BUILD_TYPE)
        set(CMAKE_BUILD_TYPE "Release" CACHE STRING "" FORCE)
    endif()
endif()

# Grab the current CBMC version from config.inc
# We do this so we have a matching cbmc version between the Makefile build and
# the CMake build. This version info is useful for things like generating
# packages (which usually need to contain version info in their metadata and
# filenames)
file(
  STRINGS src/config.inc CBMC_VERSION
  REGEX "CBMC_VERSION = (.*)")
string(REGEX REPLACE "CBMC_VERSION = (.*)" "\\1" CBMC_VERSION ${CBMC_VERSION})

project(CBMC VERSION ${CBMC_VERSION})

# when config.inc changes we’ll need to reconfigure to check if the version changed
set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/src/config.inc")

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
    set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O2 -g")
    #   Enable lots of warnings
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wpedantic -Werror -Wno-deprecated-declarations -Wswitch-enum")
elseif("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
    # This would be the place to enable warnings for Windows builds, although
    # config.inc doesn't seem to do that currently

    # Include Git Bash Environment (rqeuired for download_project (patch))
    find_package(Git)
    if(GIT_FOUND)
        get_filename_component(git_root ${GIT_EXECUTABLE} DIRECTORY)
        set(ENV{PATH} "${git_root}\\..\\usr\\bin;$ENV{PATH}")
    else()
        message(FATAL_ERROR "Git not found. Git bash is required to configure the build.")
    endif()
endif()

set(enable_cbmc_tests on CACHE BOOL "Whether CBMC tests should be enabled")

set(sat_impl "minisat2" CACHE STRING
    "This setting controls the SAT library which is used. Valid values are
    'minisat2', 'glucose', 'cadical', 'ipasir-cadical' or 'ipasir-custom'"
)

if(${enable_cbmc_tests})
    enable_testing()
endif()

if(DEFINED CMAKE_USE_CUDD)
    include("${CMAKE_CURRENT_SOURCE_DIR}/cmake/DownloadProject.cmake")
    message(STATUS "Downloading Cudd-3.0.0")
    download_project(PROJ cudd
            URL https://sourceforge.net/projects/cudd-mirror/files/cudd-3.0.0.tar.gz/download
            URL_MD5 4fdafe4924b81648b908881c81fe6c30
            )

    if(NOT EXISTS ${cudd_SOURCE_DIR}/Makefile)
        message(STATUS "Configuring Cudd-3.0.0")
        execute_process(COMMAND ./configure WORKING_DIRECTORY ${cudd_SOURCE_DIR})
    endif()
    message(STATUS "Building Cudd-3.0.0")
    execute_process(COMMAND make WORKING_DIRECTORY ${cudd_SOURCE_DIR})

    add_library(cudd STATIC IMPORTED)
    set_property(TARGET cudd PROPERTY IMPORTED_LOCATION ${cudd_SOURCE_DIR}/cudd/.libs/libcudd.a)

    add_library(cudd-cplusplus STATIC IMPORTED)
    set_property(TARGET cudd-cplusplus PROPERTY IMPORTED_LOCATION ${cudd_SOURCE_DIR}/cplusplus/.libs/libobj.a)

    include_directories(${cudd_SOURCE_DIR})
    add_compile_options(-DHAVE_CUDD)
    set(CUDD_INCLUDE ${cudd_SOURCE_DIR} CACHE STRING "Record Cudd directory for includes")
endif()

if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang" OR
   "${CMAKE_CXX_COMPILER_ID}" STREQUAL "AppleClang" OR
   "${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU"
)
    option(enable_coverage "Build with coverage recording")
    set(parallel_tests "1" CACHE STRING "Number of tests to run in parallel")
    if(enable_coverage)
        add_compile_options(--coverage -g)
        set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} --coverage -g")
        if (NOT DEFINED CODE_COVERAGE_OUTPUT_DIR)
            set(CODE_COVERAGE_OUTPUT_DIR ${CMAKE_BINARY_DIR}/html)
            set(CODE_COVERAGE_INFO_FILE ${CODE_COVERAGE_OUTPUT_DIR}/coverage.info)
        endif()
        find_program(CODE_COVERAGE_LCOV lcov)
        find_program(CODE_COVERAGE_GENHTML genhtml)
        add_custom_target(coverage
            COMMAND ${CMAKE_COMMAND} -E make_directory ${CODE_COVERAGE_OUTPUT_DIR}
            COMMAND ctest -V -L CORE -j${parallel_tests}
            COMMAND ${CODE_COVERAGE_LCOV} ${LCOV_FLAGS} --capture --directory ${CMAKE_BINARY_DIR} --output-file ${CODE_COVERAGE_INFO_FILE}
            COMMAND ${CODE_COVERAGE_LCOV} ${LCOV_FLAGS} --remove ${CODE_COVERAGE_INFO_FILE} '/usr/*' --output-file ${CODE_COVERAGE_INFO_FILE}
            COMMAND ${CODE_COVERAGE_GENHTML} ${CODE_COVERAGE_INFO_FILE} --output-directory ${CODE_COVERAGE_OUTPUT_DIR}
            DEPENDS
              "$<TARGET_FILE:java-unit>"
              "$<TARGET_FILE:unit>"
              "$<TARGET_FILE:goto-harness>"
              "$<TARGET_FILE:cbmc>"
              "$<TARGET_FILE:crangler>"
              "$<TARGET_FILE:driver>"
              "$<TARGET_FILE:goto-analyzer>"
              "$<TARGET_FILE:goto-cc>"
              "$<TARGET_FILE:goto-diff>"
              "$<TARGET_FILE:goto-instrument>"
              "$<TARGET_FILE:janalyzer>"
              "$<TARGET_FILE:jbmc>"
              "$<TARGET_FILE:jdiff>"
              "$<TARGET_FILE:smt2_solver>"
              "$<TARGET_FILE:symtab2gb>"
              "libour_archive.a"
            WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
        )
    endif()
endif()

if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang" OR
        "${CMAKE_CXX_COMPILER_ID}" STREQUAL "AppleClang" OR
        "${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU"
)
    option(enable_profiling "Build with profiling data")
    if(enable_profiling)
        add_compile_options(-g -pg)
        set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pg")
        set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -pg")
    endif()
endif()

function(cprover_default_properties)
    set(CBMC_CXX_STANDARD 11)
    set(CBMC_CXX_STANDARD_REQUIRED true)
    set(CBMC_XCODE_ATTRIBUTE_CODE_SIGN_IDENTITY
            "Developer ID Application: Daniel Kroening")

    set_target_properties(
      ${ARGN}
     PROPERTIES
     CXX_STANDARD ${CBMC_CXX_STANDARD}
     CXX_STANDARD_REQUIRED ${CBMC_CXX_STANDARD_REQUIRED}
     XCODE_ATTRIBUTE_CODE_SIGN_IDENTITY ${CBMC_XCODE_ATTRIBUTE_CODE_SIGN_IDENTITY})
endfunction()

if(CMAKE_SYSTEM_NAME STREQUAL Linux)
set(WITH_MEMORY_ANALYZER_DEFAULT ON)
else()
set(WITH_MEMORY_ANALYZER_DEFAULT OFF)
endif()

option(WITH_MEMORY_ANALYZER
  "build the memory analyzer" ${WITH_MEMORY_ANALYZER_DEFAULT})

add_subdirectory(src)
add_subdirectory(regression)
add_subdirectory(unit)

cprover_default_properties(
    analyses
    ansi-c
    assembler
    big-int
    cbmc
    cbmc-lib
    cpp
    crangler
    crangler-lib
    driver
    goto-analyzer
    goto-analyzer-lib
    goto-cc
    goto-cc-lib
    goto-checker
    goto-diff
    goto-diff-lib
    goto-harness
    goto-instrument
    goto-instrument-lib
    goto-programs
    goto-symex
    jsil
    json
    json-symtab-language
    langapi
    linking
    pointer-analysis
    solvers
    statement-list
    symtab2gb
    testing-utils
    unit
    util
    xml)

option(WITH_JBMC "Build the JBMC Java front-end" ON)
if(WITH_JBMC)
    add_subdirectory(jbmc)
endif()

include(cmake/packaging.cmake)
