cmake_minimum_required(VERSION 3.2)

set(CMAKE_OSX_DEPLOYMENT_TARGET 10.9)

include(GNUInstallDirs)

set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

add_subdirectory(src)

set(enable_cbmc_tests on CACHE BOOL "Whether CBMC tests should be enabled")

if(${enable_cbmc_tests})
    enable_testing()
endif()
add_subdirectory(unit)
add_subdirectory(regression)
