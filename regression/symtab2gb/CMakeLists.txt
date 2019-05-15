add_test_pl_tests(
  "${CMAKE_CURRENT_SOURCE_DIR}/chain.sh $<TARGET_FILE:symtab2gb> $<TARGET_FILE:cbmc>"
)
