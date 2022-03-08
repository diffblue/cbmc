# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/jdiff_main.cpp
)
add_library(jdiff-lib ${sources})

generic_includes(jdiff-lib)

target_link_libraries(jdiff-lib
    ansi-c
    linking
    big-int
    pointer-analysis
    goto-diff-lib
    goto-instrument-lib
    goto-programs
    java_bytecode
    langapi
    xml
    util
)

# Executable
add_executable(jdiff jdiff_main.cpp)
target_link_libraries(jdiff jdiff-lib)
install(TARGETS jdiff DESTINATION ${CMAKE_INSTALL_BINDIR})
