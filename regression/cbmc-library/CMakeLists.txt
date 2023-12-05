if(NOT WIN32)
add_test_pl_tests(
    "$<TARGET_FILE:cbmc> --no-standard-checks"
)
else()
add_test_pl_profile(
    "cbmc-library"
    "$<TARGET_FILE:cbmc> --no-standard-checks"
    "-C;-X;unix;-X;gcc-only"
    "CORE"
)
endif()
