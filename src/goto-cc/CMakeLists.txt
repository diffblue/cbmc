# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/goto_cc_main.cpp
)
add_library(goto-cc-lib ${sources})

generic_includes(goto-cc-lib)

target_link_libraries(goto-cc-lib
    big-int
    goto-programs
    util
    json
    linking
    ansi-c
    cpp
    xml
    assembler
    langapi
)

add_if_library(goto-cc-lib jsil)

# Executable
add_executable(goto-cc goto_cc_main.cpp)
target_link_libraries(goto-cc goto-cc-lib)

if(WIN32)
  set_target_properties(goto-cc PROPERTIES OUTPUT_NAME goto-cl)
else()
  add_custom_command(TARGET goto-cc
    POST_BUILD
    COMMAND "${CMAKE_COMMAND}" -E create_symlink
      goto-cc $<TARGET_FILE_DIR:goto-cc>/goto-gcc
    BYPRODUCTS ${CMAKE_BINARY_DIR}/bin/goto-gcc)
endif()
