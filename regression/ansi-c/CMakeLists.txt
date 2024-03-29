if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
    add_test_pl_tests(
        "$<TARGET_FILE:goto-cc>" -X gcc-only -X clang-only
    )
elseif("${CMAKE_SYSTEM_NAME}" STREQUAL "Darwin")
    add_test_pl_tests(
        "$<TARGET_FILE:goto-cc>"
    )

    add_test_pl_profile(
        "ansi-c-c++-front-end"
        "$<TARGET_FILE:goto-cc> -xc++ -D_Bool=bool"
        "-C;-I;test-c++-front-end;-s;c++-front-end"
        "CORE"
    )
else()
    find_program(CLANG_EXISTS "clang")
    find_program(GCC_EXISTS "gcc")
    if(CLANG_EXISTS)
        add_test_pl_profile(
            "ansi-c-clang"
            "$<TARGET_FILE:goto-cc> --native-compiler clang"
            "-C;-s;ansi-c-clang"
            "CORE"
        )
    endif()
    if(GCC_EXISTS)
        add_test_pl_profile(
            "ansi-c-gcc"
            "$<TARGET_FILE:goto-cc> --native-compiler gcc"
            "-C;-X;fake-gcc-version;-X;clang-only;-s;ansi-c-gcc"
            "CORE"
        )
        add_test_pl_profile(
            "ansi-c-fake-gcc"
            "$<TARGET_FILE:goto-cc>"
            "-C;-I;fake-gcc-version;-s;ansi-c-fake-gcc"
            "CORE"
        )
    elseif(NOT CLANG_EXISTS)
        add_test_pl_tests(
            "$<TARGET_FILE:goto-cc>" -X clang-only
        )
    endif()

    add_test_pl_profile(
        "ansi-c-c++-front-end"
        "$<TARGET_FILE:goto-cc> -xc++ -D_Bool=bool"
        "-C;-I;test-c++-front-end;-s;c++-front-end"
        "CORE"
    )
endif()
