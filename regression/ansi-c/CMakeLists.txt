if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
    add_test_pl_tests(
        "$<TARGET_FILE:goto-cc>" -X gcc-only
    )
elseif("${CMAKE_SYSTEM_NAME}" STREQUAL "Darwin")
    add_test_pl_tests(
        "$<TARGET_FILE:goto-cc>"
    )

    # In MacOS, a change in the assert.h header file
    # is causing template errors when exercising the
    # C++ front end (because of a transitive include
    # of <type_traits>) for files that include the
    # <assert.h> or <cassert> headers.
    add_test_pl_profile(
        "ansi-c-c++-front-end"
        "$<TARGET_FILE:goto-cc> -xc++ -D_Bool=bool"
        "-C;-I;test-c++-front-end;-s;c++-front-end-X;macos-assert-broken"
        "CORE"
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
