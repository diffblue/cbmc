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

# Symlink man page to cbmc man page until a real man page is written
install(CODE "execute_process( \
  COMMAND ${CMAKE_COMMAND} -E create_symlink \
  cbmc.1 \
  ${CMAKE_INSTALL_FULL_MANDIR}/man1/goto-harness.1 \
  )"
)
