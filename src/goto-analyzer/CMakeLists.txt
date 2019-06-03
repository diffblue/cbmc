# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/goto_analyzer_main.cpp
)
add_library(goto-analyzer-lib ${sources})

generic_includes(goto-analyzer-lib)

target_link_libraries(goto-analyzer-lib
    ansi-c
    cpp
    linking
    big-int
    goto-checker
    goto-programs
    analyses
    pointer-analysis
    langapi
    json
    assembler
    util
)

add_if_library(goto-analyzer-lib jsil)

# Executable
add_executable(goto-analyzer goto_analyzer_main.cpp)
target_link_libraries(goto-analyzer goto-analyzer-lib)
