set(SRC bigint-func.cc bigint.cc)

add_executable(test-bigint ${SRC} bigint-test.cc)
add_library(big-int ${SRC})

generic_includes(big-int)
