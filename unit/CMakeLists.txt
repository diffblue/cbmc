file(GLOB_RECURSE sources "*.cpp" "*.h")

file(GLOB_RECURSE testing_utils "testing-utils/*.cpp" "testing-utils/*.h")

list(REMOVE_ITEM sources
    # Used in executables
    ${CMAKE_CURRENT_SOURCE_DIR}/miniBDD.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/string_utils.cpp

    # Don't build
    ${CMAKE_CURRENT_SOURCE_DIR}/sharing_map.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/elf_reader.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/smt2_parser.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/json.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/cpp_parser.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/osx_fat_reader.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/unicode.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/wp.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/cpp_scanner.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/float_utils.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/ieee_float.cpp

    # Will be built into a separate library and linked
    ${testing_utils}

    # Intended to fail to compile
    ${CMAKE_CURRENT_SOURCE_DIR}/util/expr_cast/expr_undefined_casts.cpp
)

add_subdirectory(testing-utils)

add_executable(unit ${sources})
target_include_directories(unit
    PUBLIC
    ${CBMC_BINARY_DIR}
    ${CBMC_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}
)
target_link_libraries(unit testing-utils ansi-c solvers java_bytecode)
add_test(
    NAME unit
    COMMAND $<TARGET_FILE:unit>
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
)
set_tests_properties(unit PROPERTIES LABELS "CORE;CBMC")

add_executable(miniBDD miniBDD.cpp)
target_include_directories(miniBDD
    PUBLIC
    ${CBMC_BINARY_DIR}
    ${CBMC_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}
)
target_link_libraries(miniBDD solvers ansi-c)
add_test(NAME miniBDD COMMAND $<TARGET_FILE:miniBDD>)
set_tests_properties(miniBDD PROPERTIES LABELS "CORE;CBMC")

add_executable(string_utils string_utils.cpp)
target_include_directories(string_utils
    PUBLIC
    ${CBMC_BINARY_DIR}
    ${CBMC_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}
)
target_link_libraries(string_utils solvers ansi-c)
add_test(NAME string_utils COMMAND $<TARGET_FILE:string_utils>)
set_tests_properties(string_utils PROPERTIES LABELS "CORE;CBMC")
