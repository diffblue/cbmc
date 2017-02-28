# Library
file(GLOB_RECURSE sources "*.cpp")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/runner/cegis_main.cpp
)
add_library(cegis-lib ${sources})

generic_includes(cegis-lib)

target_link_libraries(cegis-lib
    ansi-c
    cpp
    java_bytecode
    linking
    big-int
    goto-programs
    goto-symex
    pointer-analysis
    analyses
    langapi
    xml
    assembler
    solvers
    util
    goto-instrument-lib
    cbmc-lib
)

# Executable
add_executable(cegis runner/cegis_main.cpp)
target_link_libraries(cegis cegis-lib)
