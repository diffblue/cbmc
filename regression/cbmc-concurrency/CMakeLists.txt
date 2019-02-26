if((NOT WIN32) AND (NOT APPLE))
add_test_pl_tests(
    "$<TARGET_FILE:cbmc>"
)
else()
add_test_pl_tests(
    "$<TARGET_FILE:cbmc>"
    "cbmc-concurrency"
    "$<TARGET_FILE:cbmc>"
    "-C;-X;pthread"
    "CORE"
)
endif()
