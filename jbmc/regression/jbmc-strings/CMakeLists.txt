if("${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
  set(exclude_win_broken_tests -X winbug)
else()
  set(exclude_win_broken_tests "")
endif()

add_test_pl_tests(
    "$<TARGET_FILE:jbmc> --validate-goto-model --validate-ssa-equation" ${exclude_win_broken_tests}
)

if("${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
  message(WARNING "skipping broken jbmc-strings/ tests on windows")
else()
  add_test_pl_profile(
    "jbmc-strings-symex-driven-lazy-loading"
    "$<TARGET_FILE:jbmc> --validate-goto-model --validate-ssa-equation --symex-driven-lazy-loading"
    "-C;-X;symex-driven-lazy-loading-expected-failure;-s;symex-driven-loading"
    "CORE"
    )
endif()
