# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/goto_synthesizer_main.cpp
)
add_library(goto-synthesizer-lib ${sources})

generic_includes(goto-synthesizer-lib)

target_link_libraries(goto-synthesizer-lib
    ansi-c
    cpp
    big-int
    goto-checker
    goto-instrument-lib
    goto-programs
    langapi
    util
    json
)

# Executable
add_executable(goto-synthesizer goto_synthesizer_main.cpp)
target_link_libraries(goto-synthesizer goto-synthesizer-lib)
install(TARGETS goto-synthesizer DESTINATION ${CMAKE_INSTALL_BINDIR})

# Man page
if(NOT WIN32)
  install(
    DIRECTORY ${CMAKE_SOURCE_DIR}/doc/man/
    DESTINATION ${CMAKE_INSTALL_MANDIR}/man1
    FILES_MATCHING PATTERN "goto-synthesizer*")
endif()
