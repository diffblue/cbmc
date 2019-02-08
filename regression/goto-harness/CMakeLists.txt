if(WIN32)
    set(is_windows true)
else()
    set(is_windows false)
endif()

add_test_pl_tests(
  "../chain.sh \
   $<TARGET_FILE:goto-cc> \
   $<TARGET_FILE:goto-harness> \
   $<TARGET_FILE:cbmc> \
   ${is_windows}")
