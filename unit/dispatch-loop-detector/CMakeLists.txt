file(GLOB dld_c_tests
    RELATIVE "${CMAKE_CURRENT_SOURCE_DIR}/test-files"
    "${CMAKE_CURRENT_SOURCE_DIR}/test-files/*.c"
)
set(make_string_literal
    "${CBMC_SOURCE_DIR}/../scripts/make_string_literal.sh"
)
add_custom_target(dld_string_files)
foreach(c_test ${dld_c_tests})
  set(src_path
    "${CMAKE_CURRENT_SOURCE_DIR}/test-files/${c_test}")
  set(dst_path
    "${CMAKE_CURRENT_BINARY_DIR}/test-files/${c_test}.string")

  add_custom_command(
      OUTPUT "${dst_path}"
      MAIN_DEPENDENCY "${src_path}"
      DEPENDS "${make_string_literal}"
      COMMAND ${make_string_literal} dispatch ${src_path} ${dst_path}
      VERBATIM
  )
  add_custom_target("generate_${c_test}.string" DEPENDS ${dst_path})
  add_dependencies(dld_string_files "generate_${c_test}.string")
endforeach(c_test ${dld_c_tests})

add_library(dispatch-loop-detector OBJECT
    "${CMAKE_CURRENT_SOURCE_DIR}/dispatch_loop_detector.cpp"
)
add_dependencies(dispatch-loop-detector dld_string_files)

target_include_directories(dispatch-loop-detector
    PUBLIC
    "${CMAKE_CURRENT_BINARY_DIR}/test-files"
    ${CBMC_BINARY_DIR}
    ${CBMC_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}
)
target_link_libraries(dispatch-loop-detector
    testing-utils
)
