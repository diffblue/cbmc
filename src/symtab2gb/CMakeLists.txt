add_executable(symtab2gb
        symtab2gb_main.cpp
        symtab2gb_parse_options.cpp
        symtab2gb_parse_options.h)

generic_includes(symtab2gb)

target_link_libraries(symtab2gb
        util
        ansi-c
        goto-programs
        json-symtab-language)

install(TARGETS symtab2gb DESTINATION ${CMAKE_INSTALL_BINDIR})
