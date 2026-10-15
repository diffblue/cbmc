if(WIN32)
    set(is_windows true)
else()
    set(is_windows false)
endif()

# `gcc-only': the test needs libstdc++ (the default C++ standard library of
# GCC); chain.sh passes no options to goto-cc, which then uses the host
# compiler's default C++ standard and library
if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
    set(gcc_only "")
else()
    set(gcc_only -X gcc-only)
endif()

add_test_pl_tests(
    "${CMAKE_CURRENT_SOURCE_DIR}/chain.sh $<TARGET_FILE:goto-cc> $<TARGET_FILE:cbmc> ${is_windows}"
    ${gcc_only}
)
