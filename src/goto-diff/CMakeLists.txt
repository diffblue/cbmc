# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/goto_diff_main.cpp
)
add_library(goto-diff-lib ${sources})

generic_includes(goto-diff-lib)

target_link_libraries(goto-diff-lib
    ansi-c
    cpp
    linking
    big-int
    pointer-analysis
    goto-instrument-lib
    goto-programs
    assembler
    analyses
    langapi
    xml
    util
    solvers
)

# Executable
add_executable(goto-diff goto_diff_main.cpp)
target_link_libraries(goto-diff goto-diff-lib)
install(TARGETS goto-diff DESTINATION ${CMAKE_INSTALL_BINDIR})

# Man page
if(NOT WIN32)
  install(
    DIRECTORY ${CMAKE_SOURCE_DIR}/doc/man/
    DESTINATION ${CMAKE_INSTALL_MANDIR}/man1
    FILES_MATCHING PATTERN "goto-diff*")
endif()
