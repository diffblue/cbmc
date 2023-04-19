if("${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
  set(is_windows true)
  set(exclude_win_broken_tests -X winbug)
else()
  set(is_windows false)
  set(exclude_win_broken_tests "")
endif()

add_test_pl_tests(
  "${CMAKE_CURRENT_SOURCE_DIR}/chain.sh $<TARGET_FILE:goto-cc> $<TARGET_FILE:goto-inspect> ${is_windows}" ${exclude_win_broken_tests}
)
