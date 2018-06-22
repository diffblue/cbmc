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

# based on https://cmake.org/pipermail/cmake/2010-July/038015.html
find_package(Git)
if(GIT_FOUND)
  file(WRITE ${CMAKE_BINARY_DIR}/version.cmake
    "
    file(STRINGS \${CBMC_SOURCE_DIR}/config.inc
      config_inc_v REGEX \"CBMC_VERSION *= *[0-9\.]+\")
    string(REGEX REPLACE \"^CBMC_VERSION *= *\" \"\" CBMC_RELEASE \${config_inc_v})
    execute_process(
      COMMAND \"${GIT_EXECUTABLE}\" \"describe\" \"--tags\" \"--always\" \"--dirty\"
      OUTPUT_VARIABLE GIT_INFO
      OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    configure_file(\${CUR}/version.h.in version.h)
    "
  )
else()
  file(WRITE ${CMAKE_BINARY_DIR}/version.cmake
    "
    file(STRINGS \${CBMC_SOURCE_DIR}/config.inc
      config_inc_v REGEX \"CBMC_VERSION *= *[0-9\.]+\")
    string(REGEX REPLACE \"^CBMC_VERSION *= *\" \"\" CBMC_RELEASE \${config_inc_v})
    set(GIT_INFO \"n/a\")
    configure_file(\${CUR}/version.h.in version.h)
    "
  )
endif()

macro(git_revision target)
  file(WRITE ${CMAKE_CURRENT_BINARY_DIR}/version.h.in
    "\#define CBMC_VERSION \"@CBMC_RELEASE@ (@GIT_INFO@)\"\n")
  add_custom_target(
    ${target}-version.h
    COMMAND ${CMAKE_COMMAND}
      -D CBMC_SOURCE_DIR=${CBMC_SOURCE_DIR}
      -D CUR=${CMAKE_CURRENT_BINARY_DIR}
      -P ${CMAKE_BINARY_DIR}/version.cmake
  )
 add_dependencies(${target} ${target}-version.h)
endmacro()
include_directories(${CMAKE_CURRENT_BINARY_DIR})

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
    clobber
    clobber-lib
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
    miniBDD
    mmcc
    pointer-analysis
    solvers
    test-bigint
    testing-utils
    unit
    util
    xml

    java_bytecode
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
