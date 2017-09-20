file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/symex_main.cpp
)
add_library(symex-lib ${sources} ${headers})

target_link_libraries(symex-lib
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
    path-symex
)

generic_includes(symex-lib)

add_if_library(symex-lib bv_refinement)
add_if_library(symex-lib java_bytecode)
add_if_library(symex-lib specc)
add_if_library(symex-lib php)

add_executable(symex symex_main.cpp)

target_link_libraries(symex symex-lib)

install(TARGETS symex DESTINATION bin)
