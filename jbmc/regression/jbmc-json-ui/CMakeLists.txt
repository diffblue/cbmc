find_program(JQ jq)
if(NOT JQ)
  message("Skipping JBMC JSON-UI tests: couldn't find jq in your path")
else()
  add_test_pl_tests(
      "${CMAKE_CURRENT_SOURCE_DIR}/chain.sh $<TARGET_FILE:jbmc>"
  )
endif()

