add_test(
  NAME goto-analyzer-get-fp-values
  COMMAND 
    python3 "${CMAKE_CURRENT_LIST_DIR}/test.py"
    "$<TARGET_FILE:goto-analyzer>"
    "${CMAKE_CURRENT_LIST_DIR}/test.c")