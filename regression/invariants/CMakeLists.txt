add_executable(driver driver.cpp)
target_link_libraries(driver big-int util)
if(ipo_supported)
  set_property(TARGET driver PROPERTY INTERPROCEDURAL_OPTIMIZATION True)
endif()

add_test_pl_tests(
    "$<TARGET_FILE:driver>"
)
