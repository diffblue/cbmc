find_program(JQ jq)
if(NOT JQ)
  message("Skipping solver-hardness tests: couldn't find jq in your path")
else()
  add_test_pl_tests(
    "../chain.sh $<TARGET_FILE:cbmc>")
endif()

