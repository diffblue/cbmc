if("${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
  set(is_windows true)
else()
  set(is_windows false)
endif()

add_test_pl_tests(
  "${CMAKE_CURRENT_SOURCE_DIR}/chain.sh $<TARGET_FILE:goto-cc> $<TARGET_FILE:goto-inspect> ${is_windows}"
)
