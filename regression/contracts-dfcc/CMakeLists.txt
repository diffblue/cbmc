if(WIN32)
  set(is_windows true)
else()
  set(is_windows false)
endif()

if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
  set(gcc_only -X gcc-only)
  set(gcc_only_string "-X;gcc-only;")
else()
  set(gcc_only "")
  set(gcc_only_string "")
endif()


set(dfcc_cmd
    "${CMAKE_CURRENT_SOURCE_DIR}/chain.sh $<TARGET_FILE:goto-cc> $<TARGET_FILE:goto-instrument> $<TARGET_FILE:cbmc> ${is_windows} true")
set(dfcc_core_shards 4)

# The CORE run of this suite is one of the slowest non-sharded CORE ctests;
# shard it (and keep its 30-minute per-shard timeout) so it runs as several
# parallel ctest entries on the macOS runners. See add_sharded_test_pl_tests.
add_sharded_test_pl_tests(
    "${dfcc_cmd}" "dfcc-core" ${dfcc_core_shards} 1800 ${gcc_only})

add_test_pl_profile(
    "contracts-non-dfcc"
    "${CMAKE_CURRENT_SOURCE_DIR}/chain.sh $<TARGET_FILE:goto-cc> $<TARGET_FILE:goto-instrument> $<TARGET_FILE:cbmc> ${is_windows} false" ${gcc_only}
    "-C;-X;dfcc-only;-s;non-dfcc"
    "CORE"
)

## Enabling these causes a very significant increase in the time taken to run the regressions

#add_test_pl_profile(
#    "cbmc-z3"
#    "${CMAKE_CURRENT_SOURCE_DIR}/chain.sh $<TARGET_FILE:goto-cc> $<TARGET_FILE:goto-instrument> '$<TARGET_FILE:cbmc> --z3' ${is_windows} true"
#    "-C;-X;broken-smt-backend;-X;thorough-smt-backend;-X;broken-z3-backend;-X;thorough-z3-backend;${gcc_only_string}-s;z3"
#    "CORE"
#)

#add_test_pl_profile(
#    "cbmc-cprover-smt2"
#    "${CMAKE_CURRENT_SOURCE_DIR}/chain.sh $<TARGET_FILE:goto-cc> $<TARGET_FILE:goto-instrument> '$<TARGET_FILE:cbmc> --cprover-smt2' ${is_windows} true"
#    "-C;-X;broken-smt-backend;-X;thorough-smt-backend;-X;broken-cprover-smt2-backend;-X;thorough-cprover-smt2-backend;${gcc_only_string}-s;cprover-smt2"
#    "CORE"
#)

# solver appears on the PATH in Windows already
if(NOT "${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
  foreach(shard RANGE 1 ${dfcc_core_shards})
    set_property(
      TEST "contracts-dfcc-${shard}-CORE"
      PROPERTY ENVIRONMENT
        "PATH=$ENV{PATH}:$<TARGET_FILE_DIR:smt2_solver>"
    )
  endforeach()
  set_property(
    TEST "contracts-non-dfcc-CORE"
    PROPERTY ENVIRONMENT
      "PATH=$ENV{PATH}:$<TARGET_FILE_DIR:smt2_solver>"
  )
endif()
