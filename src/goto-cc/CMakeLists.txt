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
      goto-cc $<TARGET_FILE_DIR:goto-cc>/goto-gcc)
endif()

set(cbmc_version_files as_mode.cpp compile.cpp gcc_mode.cpp goto_cc_mode.cpp)
git_revision(goto-cc-lib cbmc_version_files)
