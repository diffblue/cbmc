# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/goto_instrument_main.cpp

    # This doesn't build
    ${CMAKE_CURRENT_SOURCE_DIR}/accelerate/linearize.cpp
)
add_library(goto-inkstrument-lib ${sources})

generic_includes(goto-inkstrument-lib)

target_link_libraries(goto-inkstrument-lib
    ansi-c
    cpp
    inking
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

add_if_library(goto-inkstrument-lib java_bytecode)
add_if_library(goto-inkstrument-lib glpk)

# Executable
add_executable(goto-inkstrument goto_instrument_main.cpp)
target_link_libraries(goto-inkstrument goto-inkstrument-lib)
