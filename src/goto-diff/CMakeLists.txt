# Library
file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/goto_diff_main.cpp
)
add_library(goto-diff-lib ${sources} ${headers})

generic_includes(goto-diff-lib)

target_link_libraries(goto-diff-lib
    ansi-c
    cpp
    linking
    big-int
    pointer-analysis
    goto-programs
    assembler
    analyses
    langapi
    xml
    util
    solvers
)

add_if_library(goto-diff-lib java_bytecode)
add_if_library(goto-diff-lib jsil)
add_if_library(goto-diff-lib php)

# Executable
add_executable(goto-diff goto_diff_main.cpp)
target_link_libraries(goto-diff goto-diff-lib)
