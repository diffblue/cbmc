add_test_pl_profile(
    "cbmc-incr-smt2-z3"
    "$<TARGET_FILE:cbmc> --incremental-smt2-solver 'z3 --smt2 -in' --validate-goto-model --validate-ssa-equation"
    "-C;-s;new-smt-z3"
    "CORE"
)

add_test_pl_profile(
    "cbmc-incr-smt2-cvc5"
    "$<TARGET_FILE:cbmc> --incremental-smt2-solver 'cvc5 --lang=smtlib2.6 --incremental' --validate-goto-model --validate-ssa-equation"
    "-C;-s;new-smt-cvc5"
    "CORE"
)
