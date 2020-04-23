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
  install(TARGETS goto-cl DESTINATION ${CMAKE_INSTALL_BINDIR})
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
  install(TARGETS goto-cc DESTINATION ${CMAKE_INSTALL_BINDIR})
  install(CODE "execute_process( \
    COMMAND ${CMAKE_COMMAND} -E create_symlink \
    goto-cc \
    ${CMAKE_INSTALL_FULL_BINDIR}/goto-gcc \
    )"
  )
  install(CODE "execute_process( \
    COMMAND ${CMAKE_COMMAND} -E create_symlink \
    goto-cc \
    ${CMAKE_INSTALL_FULL_BINDIR}/goto-ld \
    )"
  )
  # Symlink man page to cbmc man page until a real man page is written
  install(CODE "execute_process( \
    COMMAND ${CMAKE_COMMAND} -E create_symlink \
    cbmc.1 \
    ${CMAKE_INSTALL_FULL_MANDIR}/man1/goto-cc.1 \
    )"
  )
  install(CODE "execute_process( \
    COMMAND ${CMAKE_COMMAND} -E create_symlink \
    cbmc.1 \
    ${CMAKE_INSTALL_FULL_MANDIR}/man1/goto-gcc.1 \
    )"
  )
  install(CODE "execute_process( \
    COMMAND ${CMAKE_COMMAND} -E create_symlink \
    cbmc.1 \
    ${CMAKE_INSTALL_FULL_MANDIR}/man1/goto-ld.1 \
    )"
  )
endif()
