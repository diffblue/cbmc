# Library
file(GLOB_RECURSE sources "*.cpp")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/clobber_main.cpp
)
add_library(clobber-lib ${sources})

generic_includes(clobber-lib)

target_link_libraries(clobber-lib
    ansi-c
    cpp
    linking
    big-int
    goto-programs
    analyses
    langapi
    xml
    assembler
    solvers
    util
    goto-symex
    pointer-analysis
    goto-instrument-lib
)

add_if_library(clobber-lib bv_refinement)
add_if_library(clobber-lib java_bytecode)
add_if_library(clobber-lib specc)
add_if_library(clobber-lib php)

# Executable
add_executable(clobber clobber_main.cpp)
target_link_libraries(clobber clobber-lib)

