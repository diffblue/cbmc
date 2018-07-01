file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(util ${sources})

generic_includes(util)

target_link_libraries(util big-int langapi)

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

file(WRITE ${CMAKE_CURRENT_BINARY_DIR}/version.h.in
  "\#define CBMC_VERSION \"@CBMC_RELEASE@ (@GIT_INFO@)\"\n")
add_custom_target(
  version.h
  COMMAND ${CMAKE_COMMAND}
    -D CBMC_SOURCE_DIR=${CBMC_SOURCE_DIR}
    -D CUR=${CMAKE_CURRENT_BINARY_DIR}
    -P ${CMAKE_BINARY_DIR}/version.cmake
)
add_dependencies(util version.h)
