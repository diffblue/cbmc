cmake_minimum_required(VERSION 3.2)

include(GNUInstallDirs)

set(CMAKE_OSX_DEPLOYMENT_TARGET 10.9)

add_subdirectory(src)

enable_testing()
add_subdirectory(unit)
