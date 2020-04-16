# TARGET_FILE (as used in other directories) can't be used with goto-gcc as it
# isn't marked as an executable (target), which CMake requires. Thus construct a
# path in the same way the symbolic link is created in the goto-cc directory.
add_test_pl_tests("$<TARGET_FILE_DIR:goto-cc>/goto-ld")
