add_test_pl_tests(
    "$<TARGET_FILE:jbmc>"
)

add_test_pl_profile(
    "strings-smoke-tests-symex-driven-lazy-loading"
    "$<TARGET_FILE:jbmc> --symex-driven-lazy-loading"
    "-C;-X;symex-driven-lazy-loading-expected-failure;-s;symex-driven-loading"
    "CORE"
)
