find_program(Z3_SOLVER z3)
find_program(CVC5_SOLVER cvc5)

set(CBMC_OUTPUT_FILE_EXTRA_ARGS "-f")
if(NOT CVC5_SOLVER)
  list(APPEND CBMC_OUTPUT_FILE_EXTRA_ARGS "-X" "cvc5")
endif()
if(NOT Z3_SOLVER)
  list(APPEND CBMC_OUTPUT_FILE_EXTRA_ARGS "-X" "z3")
endif()

add_test_pl_tests(
    "${CMAKE_CURRENT_SOURCE_DIR}/chain.py $<TARGET_FILE:cbmc>"
    ${CBMC_OUTPUT_FILE_EXTRA_ARGS}
)
