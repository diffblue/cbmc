if(NOT WIN32)
add_test_pl_tests(
    "$<TARGET_FILE:cbmc>"
)
else()
add_test_pl_tests(
    "$<TARGET_FILE:cbmc>"
    "cbmc-library"
    "$<TARGET_FILE:cbmc>"
    "-C;-X;pthread;-X;gcc-only"
    "CORE"
)
endif()
