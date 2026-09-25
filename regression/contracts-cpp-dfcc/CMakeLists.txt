if(WIN32)
  set(is_windows true)
else()
  set(is_windows false)
endif()

if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC" OR
   NOT "${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
  set(gcc_only -X gcc-only)
else()
  set(gcc_only "")
endif()

add_test_pl_tests(
    "${CMAKE_CURRENT_SOURCE_DIR}/chain.sh $<TARGET_FILE:goto-cc> $<TARGET_FILE:goto-instrument> $<TARGET_FILE:cbmc> ${is_windows} true" ${gcc_only}
)
