if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
add_test_pl_tests(
    "$<TARGET_FILE:goto-cc>" -X gcc-only
)
else()
add_test_pl_tests(
    "$<TARGET_FILE:goto-cc>"
)
add_test_pl_profile(
    "ansi-c-c++-front-end"
    "$<TARGET_FILE:goto-cc> -xc++ -D_Bool=bool"
    "-C;-I;test-c++-front-end;-s;c++-front-end"
    "CORE"
)
endif()
