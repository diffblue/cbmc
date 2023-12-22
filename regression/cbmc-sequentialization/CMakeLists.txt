if(NOT WIN32)
  add_test_pl_tests(
          "$<TARGET_FILE:cbmc> --validate-goto-model --validate-ssa-equation"
  )
else()
  add_test_pl_tests(
          "$<TARGET_FILE:cbmc> --validate-goto-model --validate-ssa-equation"
          -X requires_posix_only_headers
  )
endif()
