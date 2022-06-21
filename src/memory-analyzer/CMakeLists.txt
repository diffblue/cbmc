# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/memory-analyzer_main.cpp
)
add_library(memory-analyzer-lib ${sources})

generic_includes(memory-analyzer-lib)

target_link_libraries(memory-analyzer-lib
    ansi-c
    goto-programs
    util
)


# Executable
add_executable(memory-analyzer memory_analyzer_main.cpp)
target_link_libraries(memory-analyzer memory-analyzer-lib)

cprover_default_properties(memory-analyzer memory-analyzer-lib)

# Man page
if(NOT WIN32)
  install(
    DIRECTORY ${CMAKE_SOURCE_DIR}/doc/man/
    DESTINATION ${CMAKE_INSTALL_MANDIR}/man1
    FILES_MATCHING PATTERN "memory-analyzer*")
endif()
