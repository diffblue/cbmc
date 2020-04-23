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

add_if_library(goto-diff-lib jsil)

# Executable
add_executable(goto-diff goto_diff_main.cpp)
target_link_libraries(goto-diff goto-diff-lib)
install(TARGETS goto-diff DESTINATION ${CMAKE_INSTALL_BINDIR})

# Symlink man page to cbmc man page until a real man page is written
install(CODE "execute_process( \
  COMMAND ${CMAKE_COMMAND} -E create_symlink \
  cbmc.1 \
  ${CMAKE_INSTALL_FULL_MANDIR}/man1/goto-diff.1 \
  )"
)
