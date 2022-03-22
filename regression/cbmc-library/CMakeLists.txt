if(NOT WIN32)
add_test_pl_tests(
    "$<TARGET_FILE:cbmc>"
)
else()
add_test_pl_profile(
    "cbmc-library"
    "$<TARGET_FILE:cbmc>"
    "-C;-X;unix"
    "CORE"
)
endif()
