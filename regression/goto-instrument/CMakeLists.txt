if(WIN32)
    set(is_windows true)
else()
    set(is_windows false)
endif()

if("${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
  set(exclude_win_broken_tests -X winbug)
else()
  set(exclude_win_broken_tests "")
endif()

add_test_pl_tests(
    "${CMAKE_CURRENT_SOURCE_DIR}/chain.sh $<TARGET_FILE:goto-cc> $<TARGET_FILE:goto-instrument> $<TARGET_FILE:cbmc> ${is_windows}" ${exclude_win_broken_tests}
)
