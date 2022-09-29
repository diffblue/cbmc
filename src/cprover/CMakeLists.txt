# Library
file(GLOB_RECURSE sources "*.c" "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/cprover_main.cpp
)
add_library(cprover-lib ${sources})

generic_includes(cprover-lib)

target_link_libraries(cprover-lib
    analyses
    ansi-c
    assembler
    big-int
    cpp
    goto-checker
    goto-instrument-lib
    goto-programs
    goto-symex
    json
    json-symtab-language
    langapi
    linking
    pointer-analysis
    solvers
    statement-list
    util
    xml
)

add_if_library(cprover-lib bv_refinement)
add_if_library(cprover-lib jsil)

# Executable
add_executable(cprover cprover_main.cpp)
if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
# There is a cyclic dependency between analyses and ansi-c, which the
# Makefile-based build system resolves by using --start-group, --end-group.
# CMake lacks direct support (cf.
# https://gitlab.kitware.com/cmake/cmake/-/issues/21511), so we ensure all
# object files from libanalyses.a remain present.
target_link_libraries(cprover
  cprover-lib
  -Wl,--whole-archive -Wl,${CMAKE_BINARY_DIR}/lib/libanalyses.a -Wl,--no-whole-archive
)
else()
target_link_libraries(cprover cprover-lib)
endif()
install(TARGETS cprover DESTINATION ${CMAKE_INSTALL_BINDIR})
