add_test_pl_tests(
    "$<TARGET_FILE:jbmc> --validate-goto-model --validate-ssa-equation --validate-trace"
)

if(DEFINED BDD_GUARDS)
    add_test_pl_profile(
            "jbmc-symex-driven-lazy-loading"
            "$<TARGET_FILE:jbmc> --validate-goto-model --validate-ssa-equation --validate-trace --symex-driven-lazy-loading"
            "-C;-X;symex-driven-lazy-loading-expected-failure;-s;symex-driven-loading"
            "CORE"
    )
else()
    add_test_pl_profile(
            "jbmc-symex-driven-lazy-loading"
            "$<TARGET_FILE:jbmc> --validate-goto-model --validate-ssa-equation --validate-trace --symex-driven-lazy-loading"
            "-C;-X;symex-driven-lazy-loading-expected-failure;-X;bdd-expected-timeout;-s;symex-driven-loading"
            "CORE"
    )
endif()
