file(GLOB_RECURSE sources "*.cpp" "*.h")

# This step builds the API in the form of a statically linked library (libcprover-api-cpp.a)
add_library(cprover-api-cpp ${sources})
generic_includes(cprover-api-cpp)
target_link_libraries(cprover-api-cpp goto-checker goto-programs util langapi ansi-c)
