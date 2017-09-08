# Library
file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/goto_analyzer_main.cpp
)
add_library(goto-analyzer-lib ${sources} ${headers})

generic_includes(goto-analyzer-lib)

target_link_libraries(goto-analyzer-lib
    ansi-c
    cpp
    linking
    big-int
    goto-programs
    analyses
    pointer-analysis
    langapi
    json
    assembler
    util
)

add_if_library(goto-analyzer-lib java_bytecode)
add_if_library(goto-analyzer-lib jsil)
add_if_library(goto-analyzer-lib specc)
add_if_library(goto-analyzer-lib php)

# Executable
add_executable(goto-analyzer goto_analyzer_main.cpp)
target_link_libraries(goto-analyzer goto-analyzer-lib)
