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

# Symlink man page to cbmc man page until a real man page is written
install(CODE "execute_process( \
  COMMAND ${CMAKE_COMMAND} -E create_symlink \
  cbmc.1 \
  ${CMAKE_INSTALL_FULL_MANDIR}/man1/janalyzer.1 \
  )"
)
