file(GLOB_RECURSE sources "*.cpp" "*.h")
add_executable(goto-harness ${sources})
generic_includes(goto-harness)

target_link_libraries(goto-harness
  util
  goto-programs
  goto-instrument-lib
  json
  json-symtab-language
)
