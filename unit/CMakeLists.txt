set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED true)

file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
list(REMOVE_ITEM sources
    # Used in executables
    ${CMAKE_CURRENT_SOURCE_DIR}/miniBDD.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/string_utils.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/sharing_node.cpp

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
)

add_executable(unit ${sources} ${headers})
target_include_directories(unit
    PUBLIC
    ${CBMC_BINARY_DIR}
    ${CBMC_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}
)
target_link_libraries(unit ansi-c solvers java_bytecode)
add_test(NAME unit COMMAND unit WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})

add_executable(miniBDD miniBDD.cpp)
target_include_directories(miniBDD
    PUBLIC
    ${CBMC_BINARY_DIR}
    ${CBMC_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}
)
target_link_libraries(miniBDD solvers ansi-c)
add_test(miniBDD miniBDD)

add_executable(string_utils string_utils.cpp)
target_include_directories(string_utils
    PUBLIC
    ${CBMC_BINARY_DIR}
    ${CBMC_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}
)
target_link_libraries(string_utils solvers ansi-c)
add_test(string_utils string_utils)

add_executable(sharing_node sharing_node.cpp)
target_include_directories(sharing_node
    PUBLIC
    ${CBMC_BINARY_DIR}
    ${CBMC_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}
)
add_test(sharing_node sharing_node)

install(TARGETS unit miniBDD string_utils sharing_node DESTINATION bin)
