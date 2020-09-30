if("${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
  set(exclude_win_broken_tests -X winbug)
else()
  set(exclude_win_broken_tests "")
endif()

add_test_pl_tests(
    "$<TARGET_FILE:jbmc> --validate-goto-model --validate-ssa-equation --validate-trace" ${exclude_win_broken_tests}
)

if(DEFINED BDD_GUARDS)
    add_test_pl_profile(
            "jbmc-symex-driven-lazy-loading"
            "$<TARGET_FILE:jbmc> --validate-goto-model --validate-ssa-equation --validate-trace --symex-driven-lazy-loading"
            "-C;-X;symex-driven-lazy-loading-expected-failure;-s;symex-driven-loading"
            "CORE"
            ${exclude_win_broken_tests}
    )
else()
    add_test_pl_profile(
            "jbmc-symex-driven-lazy-loading"
            "$<TARGET_FILE:jbmc> --validate-goto-model --validate-ssa-equation --validate-trace --symex-driven-lazy-loading"
            "-C;-X;symex-driven-lazy-loading-expected-failure;-X;bdd-expected-timeout;-s;symex-driven-loading"
            "CORE"
            ${exclude_win_broken_tests}
    )
endif()
