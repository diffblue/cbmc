# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/goto_instrument_main.cpp
)
add_library(goto-instrument-lib ${sources})

generic_includes(goto-instrument-lib)

target_link_libraries(goto-instrument-lib
    ansi-c
    cpp
    linking
    big-int
    goto-programs
    goto-symex
    assembler
    pointer-analysis
    analyses
    langapi
    xml
    util
    json
    solvers
)

add_if_library(goto-instrument-lib glpk)

# Executable
add_executable(goto-instrument goto_instrument_main.cpp)
target_link_libraries(goto-instrument goto-instrument-lib)
install(TARGETS goto-instrument DESTINATION ${CMAKE_INSTALL_BINDIR})

# Symlink man page to cbmc man page until a real man page is written
install(CODE "execute_process( \
  COMMAND ${CMAKE_COMMAND} -E create_symlink \
  cbmc.1 \
  ${CMAKE_INSTALL_FULL_MANDIR}/man1/goto-instrument.1 \
  )"
)
