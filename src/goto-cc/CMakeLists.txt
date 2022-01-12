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

install(TARGETS goto-cc DESTINATION ${CMAKE_INSTALL_BINDIR})

if(WIN32)
  set_target_properties(goto-cc PROPERTIES OUTPUT_NAME goto-cl)
else()
  add_custom_command(TARGET goto-cc
    POST_BUILD
    COMMAND "${CMAKE_COMMAND}" -E create_symlink
      goto-cc $<TARGET_FILE_DIR:goto-cc>/goto-gcc
    BYPRODUCTS ${CMAKE_BINARY_DIR}/bin/goto-gcc)
  add_custom_command(TARGET goto-cc
    POST_BUILD
    COMMAND "${CMAKE_COMMAND}" -E create_symlink
      goto-cc $<TARGET_FILE_DIR:goto-cc>/goto-ld
    BYPRODUCTS ${CMAKE_BINARY_DIR}/bin/goto-ld)
  add_custom_command(TARGET goto-cc
    POST_BUILD
    COMMAND "${CMAKE_COMMAND}" -E copy
      ${CMAKE_CURRENT_SOURCE_DIR}/../../scripts/ls_parse.py
      $<TARGET_FILE_DIR:goto-cc>/ls_parse.py
    BYPRODUCTS ${CMAKE_BINARY_DIR}/bin/ls_parse.py)

  install(
    FILES
      ${CMAKE_BINARY_DIR}/bin/goto-ld
      ${CMAKE_BINARY_DIR}/bin/goto-gcc
      ${CMAKE_BINARY_DIR}/bin/ls_parse.py
    DESTINATION
      ${CMAKE_INSTALL_BINDIR})
endif()
