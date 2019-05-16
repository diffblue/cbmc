add_test_pl_tests(
  "../chain.sh \
   $<TARGET_FILE:goto-cc> \
   $<TARGET_FILE:goto-harness> \
   $<TARGET_FILE:memory-analyzer> \
   $<TARGET_FILE:cbmc> \
   ../../../build/bin/goto-gcc")
