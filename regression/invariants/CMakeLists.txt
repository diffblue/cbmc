add_executable(driver driver.cpp)
target_link_libraries(driver big-int util)

add_test_pl_tests(
    "invariants"
    "$<TARGET_FILE:driver>"
)
