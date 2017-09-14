# Library
file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/goto_instrument_main.cpp

    # This doesn't build
    ${CMAKE_CURRENT_SOURCE_DIR}/accelerate/linearize.cpp
)
add_library(goto-instrument-lib ${sources} ${headers})

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

add_if_library(goto-instrument-lib java_bytecode)
add_if_library(goto-instrument-lib glpk)

# Executable
add_executable(goto-instrument goto_instrument_main.cpp)
target_link_libraries(goto-instrument goto-instrument-lib)
