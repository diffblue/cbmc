if(WIN32)
    set(is_windows true)
    set(exclude_broken_windows_tests -X winbug)
else()
    set(is_windows false)
    set(exclude_broken_windows_tests "")
endif()

add_test_pl_tests(
    "${CMAKE_CURRENT_SOURCE_DIR}/chain.sh $<TARGET_FILE:goto-cc> $<TARGET_FILE:cbmc> ${is_windows}" ${exclude_broken_windows_tests}
)
