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
install(TARGETS goto-harness DESTINATION ${CMAKE_INSTALL_BINDIR})

# Man page
if(NOT WIN32)
  install(
    DIRECTORY ${CMAKE_SOURCE_DIR}/doc/man/
    DESTINATION ${CMAKE_INSTALL_MANDIR}/man1
    FILES_MATCHING PATTERN "goto-harness*")
endif()
