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
    analyses
    java_bytecode
    langapi
    xml
    util
)

# Executable
add_executable(jdiff jdiff_main.cpp)
target_link_libraries(jdiff jdiff-lib)
install(TARGETS jdiff DESTINATION ${CMAKE_INSTALL_BINDIR})

# Symlink man page to cbmc man page until a real man page is written
install(CODE "execute_process( \
  COMMAND ${CMAKE_COMMAND} -E create_symlink \
  cbmc.1 \
  ${CMAKE_INSTALL_FULL_MANDIR}/man1/jdiff.1 \
  )"
)
