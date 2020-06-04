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
install(TARGETS goto-analyzer DESTINATION ${CMAKE_INSTALL_BINDIR})

# Symlink man page to cbmc man page until a real man page is written
install(CODE "execute_process( \
  COMMAND ${CMAKE_COMMAND} -E create_symlink \
  cbmc.1 \
  ${CMAKE_INSTALL_FULL_MANDIR}/man1/goto-analyzer.1 \
  )"
)
