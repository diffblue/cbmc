if("${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
  set(exclude_win_broken_tests -X winbug)
else()
  set(exclude_win_broken_tests "")
endif()

add_test_pl_tests(
    "perl ../timeout.pl 8 $<TARGET_FILE:cbmc> --slice-formula" ${exclude_win_broken_tests}
)
