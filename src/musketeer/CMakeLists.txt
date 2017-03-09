# Library
file(GLOB_RECURSE sources "*.cpp")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/musketeer_main.cpp
)
add_library(musketeer-lib ${sources})

generic_includes(musketeer-lib)

target_link_libraries(musketeer-lib
    ansi-c
    linking
    big-int
    goto-programs
    goto-symex
    assembler
    pointer-analysis
    analyses
    langapi
    util
    solvers
    goto-instrument-lib
)

add_if_library(musketeer-lib glpk)

# Executable
add_executable(musketeer musketeer_main.cpp)
target_link_libraries(musketeer musketeer-lib)
