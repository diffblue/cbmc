# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/janalyzer_main.cpp
)
add_library(janalyzer-lib ${sources})

generic_includes(janalyzer-lib)

target_link_libraries(janalyzer-lib
    ansi-c
    java_bytecode
    linking
    big-int
    goto-analyzer-lib
    goto-programs
    analyses
    pointer-analysis
    langapi
    json
    util
)

# Executable
add_executable(janalyzer janalyzer_main.cpp)
target_link_libraries(janalyzer janalyzer-lib)
install(TARGETS janalyzer DESTINATION ${CMAKE_INSTALL_BINDIR})
