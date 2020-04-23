# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/jbmc_main.cpp
)
add_library(jbmc-lib ${sources})

generic_includes(jbmc-lib)

target_link_libraries(jbmc-lib
    analyses
    ansi-c
    big-int
    cbmc-lib
    goto-checker
    goto-instrument-lib
    goto-programs
    goto-symex
    java_bytecode
    json
    langapi
    linking
    miniz
    pointer-analysis
    solvers
    util
    xml
)

# Executable
add_executable(jbmc jbmc_main.cpp)
target_link_libraries(jbmc jbmc-lib)
install(TARGETS jbmc DESTINATION ${CMAKE_INSTALL_BINDIR})

# Symlink man page to cbmc man page until a real man page is written
install(CODE "execute_process( \
  COMMAND ${CMAKE_COMMAND} -E create_symlink \
  cbmc.1 \
  ${CMAKE_INSTALL_FULL_MANDIR}/man1/jbmc.1 \
  )"
)
