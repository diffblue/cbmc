file(GLOB_RECURSE sources "*.cpp" "*.h")

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
      WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    )
    configure_file(\${CUR}/version.cpp.in version.cpp)
    "
  )
else()
  file(WRITE ${CMAKE_BINARY_DIR}/version.cmake
    "
    file(STRINGS \${CBMC_SOURCE_DIR}/config.inc
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
    -D CBMC_SOURCE_DIR=${CBMC_SOURCE_DIR}
    -D CUR=${CMAKE_CURRENT_BINARY_DIR}
    -P ${CMAKE_BINARY_DIR}/version.cmake
)

add_library(util
  ${sources}
  version.cpp)

add_dependencies(util generate_version_cpp)

generic_includes(util)

target_link_libraries(util big-int langapi)
