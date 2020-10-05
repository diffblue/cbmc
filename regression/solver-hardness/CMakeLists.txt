if(NOT "${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
  add_test_pl_tests(
    "../chain.sh $<TARGET_FILE:cbmc>")
else()
  message(WARNING "solver-hardness/ tests are failing on windows for unknown reasons. An investigation is pending.")
endif()

