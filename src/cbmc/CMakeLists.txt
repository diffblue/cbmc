# Library
file(GLOB_RECURSE sources "*.cpp")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/cbmc_main.cpp
)
add_library(cbmc-lib ${sources})

generic_includes(cbmc-lib)

target_link_libraries(cbmc-lib
    ansi-c
    cpp
    linking
    big-int
    goto-programs
    goto-symex
    pointer-analysis
    goto-instrument-lib
    analyses
    langapi
    xml
    assembler
    solvers
    util
    json
)

add_if_library(cbmc-lib bv_refinement)
add_if_library(cbmc-lib java_bytecode)
add_if_library(cbmc-lib jsil)
add_if_library(cbmc-lib specc)
add_if_library(cbmc-lib php)

# Executable
add_executable(cbmc cbmc_main.cpp)
target_link_libraries(cbmc cbmc-lib)
