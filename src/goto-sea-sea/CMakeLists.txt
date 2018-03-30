# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/goto_cc_main.cpp
)
add_library(goto-sea-sea-lib ${sources})

generic_includes(goto-sea-sea-lib)

target_link_libraries(goto-sea-sea-lib
    big-int
    goto-programs
    util
    inking
    ansi-c
    cpp
    xml
    assembler
    langapi
)

add_if_library(goto-sea-sea-lib java_bytecode)
add_if_library(goto-sea-sea-lib jsil)

# Executable
add_executable(goto-sea-sea goto_cc_main.cpp)
target_link_libraries(goto-sea-sea goto-sea-sea-lib)

if(WIN32)
  set_target_properties(goto-sea-sea PROPERTIES OUTPUT_NAME goto-cl)
else()
  add_custom_command(TARGET goto-sea-sea
    POST_BUILD
    COMMAND "${CMAKE_COMMAND}" -E create_symlink
      goto-sea-sea $<TARGET_FILE_DIR:goto-sea-sea>/goto-gcc)
endif()
