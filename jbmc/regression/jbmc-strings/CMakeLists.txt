add_test_pl_tests(
    "$<TARGET_FILE:jbmc> --validate-goto-model --validate-ssa-equation"
)

add_test_pl_profile(
    "jbmc-strings-fixed-size-arrays"
    "$<TARGET_FILE:jbmc> --validate-goto-model --validate-ssa-equation --max-intermediate-string-length 100 --use-fixed-size-arrays-for-bounded-strings --no-array-field-sensitivity"
    "-C;-s;fixed-size-strings;-X;limited-size-strings-expected-failure"
    "CORE"
)

add_test_pl_profile(
    "jbmc-strings-symex-driven-lazy-loading"
    "$<TARGET_FILE:jbmc> --validate-goto-model --validate-ssa-equation --symex-driven-lazy-loading"
    "-C;-X;symex-driven-lazy-loading-expected-failure;-s;symex-driven-loading"
    "CORE"
)
