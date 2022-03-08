# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/jbmc_main.cpp
)
add_library(jbmc-lib ${sources})

generic_includes(jbmc-lib)

target_link_libraries(jbmc-lib
    ansi-c
    big-int
    cbmc-lib
    goto-checker
    goto-instrument-lib
    goto-programs
    goto-symex
    java_bytecode
    json
    langapi
    linking
    miniz
    pointer-analysis
    solvers
    util
    xml
)

# Executable
add_executable(jbmc jbmc_main.cpp)
target_link_libraries(jbmc jbmc-lib)
install(TARGETS jbmc DESTINATION ${CMAKE_INSTALL_BINDIR})

# make sure java-models-library is built at least once
add_dependencies(jbmc java-models-library)
