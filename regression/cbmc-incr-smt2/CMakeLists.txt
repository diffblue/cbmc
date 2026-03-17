find_program(Z3_SOLVER z3)
find_program(CVC5_SOLVER cvc5)

if(Z3_SOLVER)
  add_test_pl_profile(
      "cbmc-incr-smt2-z3"
      "$<TARGET_FILE:cbmc> --incremental-smt2-solver 'z3 --smt2 -in' --validate-goto-model --validate-ssa-equation"
      "-C;-s;new-smt-z3"
      "CORE"
  )
endif()

if(CVC5_SOLVER)
  add_test_pl_profile(
      "cbmc-incr-smt2-cvc5"
      "$<TARGET_FILE:cbmc> --incremental-smt2-solver 'cvc5 --lang=smtlib2.6 --incremental' --validate-goto-model --validate-ssa-equation"
      "-C;-s;new-smt-cvc5"
      "CORE"
  )
endif()
