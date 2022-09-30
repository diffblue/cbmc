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

# Man page
if(NOT WIN32)
  install(
    DIRECTORY ${CMAKE_SOURCE_DIR}/doc/man/
    DESTINATION ${CMAKE_INSTALL_MANDIR}/man1
    FILES_MATCHING PATTERN "goto-instrument*")
endif()
