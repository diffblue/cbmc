if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
add_test_pl_tests(
    "$<TARGET_FILE:goto-cc>" -X gcc-only
)
else()
add_test_pl_tests(
    "$<TARGET_FILE:goto-cc>"
)
endif()
