file(GLOB_RECURSE sources "*.cpp" "*.h")
add_executable(goto-bmc ${sources})

generic_includes(goto-bmc)

target_link_libraries(goto-bmc cprover-api-cpp)
