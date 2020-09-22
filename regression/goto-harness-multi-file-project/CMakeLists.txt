if("${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
  set(exclude_win_broken_tests -X winbug)
else()
  set(exclude_win_broken_tests "")
endif()

add_test_pl_tests(
  "${CMAKE_CURRENT_LIST_DIR}/chain.sh $<TARGET_FILE:goto-cc> $<TARGET_FILE:goto-harness> $<TARGET_FILE:cbmc>" ${exclude_win_broken_tests})
