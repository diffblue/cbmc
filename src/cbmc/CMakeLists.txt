# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/cbmc_main.cpp
)
add_library(cbmc-lib ${sources})

generic_includes(cbmc-lib)

target_link_libraries(cbmc-lib
    analyses
    ansi-c
    assembler
    big-int
    cpp
    goto-instrument-lib
    goto-programs
    goto-symex
    json
    langapi
    linking
    pointer-analysis
    solvers
    util
    xml
)

add_if_library(cbmc-lib bv_refinement)
add_if_library(cbmc-lib jsil)

# Executable
add_executable(cbmc cbmc_main.cpp)
target_link_libraries(cbmc cbmc-lib)

set(cbmc_version_files cbmc_parse_options.cpp cbmc_solvers.cpp)
git_revision(cbmc-lib cbmc_version_files)
