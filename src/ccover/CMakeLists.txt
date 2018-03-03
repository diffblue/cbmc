# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/ccover_main.cpp
)
add_library(ccover-lib ${sources})

generic_includes(ccover-lib)

target_link_libraries(ccover-lib
    analyses
    ansi-c
    assembler
    big-int
    cbmc-lib
    cpp
    goto-instrument-lib
    goto-programs
    goto-symex
    java_bytecode
    json
    langapi
    linking
    pointer-analysis
    solvers
    util
    xml
)

add_if_library(ccover-lib bv_refinement)
add_if_library(ccover-lib jsil)

# Executable
add_executable(ccover ccover_main.cpp)
target_link_libraries(ccover ccover-lib)
