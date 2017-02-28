# Library
file(GLOB_RECURSE sources "*.cpp")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/goto_cc_main.cpp
)
add_library(goto-cc-lib ${sources})

generic_includes(goto-cc-lib)

target_link_libraries(goto-cc-lib
    big-int
    goto-programs
    util
    linking
    ansi-c
    cpp
    xml
    assembler
    langapi
)

add_if_library(goto-cc-lib java_bytecode)
add_if_library(goto-cc-lib jsil)

# Executable
add_executable(goto-cc goto_cc_main.cpp)
target_link_libraries(goto-cc goto-cc-lib)
