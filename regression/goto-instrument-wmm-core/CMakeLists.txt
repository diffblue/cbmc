if(WIN32)
    set(is_windows true)
else()
    set(is_windows false)
endif()

# These tests do not run with Visual Studio since they use
# gcc's asm syntax.

if(NOT WIN32)

add_test_pl_tests(
    "${CMAKE_CURRENT_SOURCE_DIR}/chain.sh $<TARGET_FILE:goto-cc> $<TARGET_FILE:goto-instrument> $<TARGET_FILE:cbmc> ${is_windows}" -X glpk
)

endif()
