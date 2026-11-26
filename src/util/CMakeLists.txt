file(GLOB_RECURSE sources "*.cpp" "*.h")

# based on https://cmake.org/pipermail/cmake/2010-July/038015.html
find_package(Git)
if(GIT_FOUND)
  file(WRITE ${CMAKE_BINARY_DIR}/version.cmake
    "
    file(STRINGS \${SRC}/src/config.inc
      config_inc_v REGEX \"CBMC_VERSION *= *[0-9\.]+\")
    string(REGEX REPLACE \"^CBMC_VERSION *= *\" \"\" CBMC_RELEASE \${config_inc_v})
    execute_process(
      COMMAND \"${GIT_EXECUTABLE}\" \"describe\" \"--tags\" \"--always\" \"--dirty\"
      OUTPUT_VARIABLE GIT_INFO
      OUTPUT_STRIP_TRAILING_WHITESPACE
      WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    )
    configure_file(\${CUR}/version.cpp.in version.cpp)
    "
  )
else()
  file(WRITE ${CMAKE_BINARY_DIR}/version.cmake
    "
    file(STRINGS \${SRC}/src/config.inc
      config_inc_v REGEX \"CBMC_VERSION *= *[0-9\.]+\")
    string(REGEX REPLACE \"^CBMC_VERSION *= *\" \"\" CBMC_RELEASE \${config_inc_v})
    set(GIT_INFO \"n/a\")
    configure_file(\${CUR}/version.cpp.in version.cpp)
    "
  )
endif()

file(WRITE ${CMAKE_CURRENT_BINARY_DIR}/version.cpp.in
  "const char *CBMC_VERSION=\"@CBMC_RELEASE@ (@GIT_INFO@)\";\n")
add_custom_target(
  generate_version_cpp
  BYPRODUCTS version.cpp
  COMMAND ${CMAKE_COMMAND}
    -D SRC=${CBMC_SOURCE_DIR}
    -D CUR=${CMAKE_CURRENT_BINARY_DIR}
    -P ${CMAKE_BINARY_DIR}/version.cmake
)

add_library(util
  ${sources}
  version.cpp)

add_dependencies(util generate_version_cpp)

generic_includes(util)

target_link_libraries(util big-int langapi)
# Link the selected memory allocator (see CBMC_ALLOCATOR in the top-level
# CMakeLists.txt) via util, so every executable and test binary that links
# util picks it up. cprover_allocator is an empty interface library when the
# system allocator is used.
target_link_libraries(util cprover_allocator)
if(WIN32)
  target_link_libraries(util dbghelp)
endif()
