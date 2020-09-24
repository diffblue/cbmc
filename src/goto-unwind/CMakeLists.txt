add_executable(goto-unwind
        src/goto_unwind_main.cpp
        src/goto_unwind_parse_options.cpp
        src/goto_unwind_parse_options.h)

target_link_libraries(goto-unwind PRIVATE goto-programs goto-instrument-lib)
