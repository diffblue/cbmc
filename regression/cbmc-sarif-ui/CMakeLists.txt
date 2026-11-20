add_test_pl_tests("$<TARGET_FILE:cbmc>")

add_test(
  NAME cbmc-sarif-validation
  COMMAND bash "${CMAKE_CURRENT_SOURCE_DIR}/test_sarif_valid.sh"
    "$<TARGET_FILE:cbmc>"
  WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
)
set_tests_properties(cbmc-sarif-validation PROPERTIES LABELS "CORE;CBMC")
