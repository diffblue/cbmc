add_test_pl_tests(
  "../chain.sh \
   $<TARGET_FILE:memory-analyzer> $<TARGET_FILE_DIR:goto-cc>/goto-gcc")
