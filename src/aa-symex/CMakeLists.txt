add_executable(aa-symex path_search.cpp)

target_link_libraries(aa-symex
    ansi-c
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
    aa-path-symex
    symex-lib
    path-symex
)

add_if_library(aa-symex bv_refinement)
add_if_library(aa-symex cpp)
add_if_library(aa-symex java_bytecode)
add_if_library(aa-symex specc)
add_if_library(aa-symex php)
