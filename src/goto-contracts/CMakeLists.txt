# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/goto_contracts_main.cpp
)
add_library(goto-contracts-lib ${sources})

generic_includes(goto-contracts-lib)

target_link_libraries(goto-contracts-lib
    ansi-c
    cpp
    big-int
    goto-programs
    langapi
    util
    json
)

# Executable
add_executable(goto-contracts goto_contracts_main.cpp)
target_link_libraries(goto-contracts goto-contracts-lib)
install(TARGETS goto-contracts DESTINATION ${CMAKE_INSTALL_BINDIR})
