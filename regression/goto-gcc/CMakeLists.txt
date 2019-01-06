# TARGET_FILE (as used in other directories) can't be used with goto-gcc as it
# isn't marked as an executable (target), which CMake requires. Thus construct a
# path in the same way the symbolic link is created in the goto-cc directory.
add_test_pl_tests("$<TARGET_FILE_DIR:goto-cc>/goto-gcc")

add_custom_command(OUTPUT "${CMAKE_CURRENT_SOURCE_DIR}/archives/libour_archive.a"
    COMMAND "$<TARGET_FILE_DIR:goto-cc>/goto-gcc" -c foo.c
    COMMAND ${CMAKE_AR} rcs libour_archive.a foo.o
    DEPENDS
      "$<TARGET_FILE_DIR:goto-cc>/goto-gcc"
      "${CMAKE_CURRENT_SOURCE_DIR}/archives/foo.c"
    WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/archives"
)

add_custom_target(libour_archive.a ALL
    DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/archives/libour_archive.a"
)
