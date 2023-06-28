file(GLOB_RECURSE sources "*.cpp" "*.h")

add_library(cli-utils
  ${sources})

add_dependencies(cli-utils util)

generic_includes(cli-utils)

target_link_libraries(cli-utils util)
