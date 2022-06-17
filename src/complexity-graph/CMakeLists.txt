
file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(complexity-graph ${sources})

generic_includes(complexity-graph)

target_link_libraries(complexity-graph goto-programs util assembler langapi analyses linking ansi-c)


## Library
#file(GLOB_RECURSE sources "*.cpp" "*.h")
#list(REMOVE_ITEM sources
#    ${CMAKE_CURRENT_SOURCE_DIR}/complexity_graph_main.cpp
#)
#add_library(complexity-graph-lib ${sources})
#
#generic_includes(complexity-graph-lib)
#
#target_link_libraries(complexity-graph-lib
#    analyses
#    ansi-c
#    assembler
#    big-int
#    complexity-graph
#    cpp
#    goto-checker
#    goto-instrument-lib
#    goto-programs
#    goto-symex
#    json
#    json-symtab-language
#    langapi
#    linking
#    pointer-analysis
#    solvers
#    statement-list
#    util
#    xml
#)
#
#add_if_library(complexity-graph-lib bv_refinement)
#add_if_library(complexity-graph-lib jsil)
#
## Executable
##add_executable(complexity-graph complexity_graph_main.cpp)
##if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
### There is a cyclic dependency between analyses and ansi-c, which the
### Makefile-based build system resolves by using --start-group, --end-group.
### CMake lacks direct support (cf.
### https://gitlab.kitware.com/cmake/cmake/-/issues/21511), so we ensure all
### object files from libanalyses.a remain present.
##target_link_libraries(complexity-graph
##  complexity-graph-lib
##  -Wl,--whole-archive -Wl,${CMAKE_BINARY_DIR}/lib/libanalyses.a -Wl,--no-whole-archive
##)
##else()
##target_link_libraries(complexity-graph complexity-graph-lib)
##endif()
##install(TARGETS complexity-graph DESTINATION ${CMAKE_INSTALL_BINDIR})
#
## Man page
#if(NOT WIN32)
#  install(
#    DIRECTORY ${CMAKE_SOURCE_DIR}/doc/man/
#    DESTINATION ${CMAKE_INSTALL_MANDIR}/man1
#    FILES_MATCHING 
#    PATTERN "c*"
#    PATTERN "g*")
#endif()
#
