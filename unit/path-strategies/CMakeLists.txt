set(path_strategy_tests
  "if_with_assertion.c"
  "case_with_assertion.c"
)
set(make_string_literal
    "${CBMC_SOURCE_DIR}/../scripts/make_string_literal.sh"
)
add_custom_target(path_strategy_string_files)
foreach(c_test ${path_strategy_tests})
  set(src_path
    "${CMAKE_CURRENT_SOURCE_DIR}/test-files/${c_test}")
  set(dst_path
    "${CMAKE_CURRENT_BINARY_DIR}/test-files/${c_test}.string")

  add_custom_command(
      OUTPUT "${dst_path}"
      MAIN_DEPENDENCY "${src_path}"
      DEPENDS "${make_string_literal}"
      COMMAND ${make_string_literal} path-strategy ${src_path} ${dst_path}
      VERBATIM
  )
  add_custom_target("generate_${c_test}.string" DEPENDS ${dst_path})
  add_dependencies(path_strategy_string_files "generate_${c_test}.string")
endforeach(c_test ${path_strategy_tests})

add_library(path-strategies OBJECT
    "${CMAKE_CURRENT_SOURCE_DIR}/path_strategies.cpp"
)
add_dependencies(path-strategies path_strategy_string_files)

target_include_directories(path-strategies
    PUBLIC
    "${CMAKE_CURRENT_BINARY_DIR}/test-files"
    ${CBMC_BINARY_DIR}
    ${CBMC_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}
)
target_link_libraries(path-strategies
    testing-utils
)
