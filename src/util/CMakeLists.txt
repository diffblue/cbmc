add_executable(irep_ids_convert irep_ids_convert.cpp)

add_custom_command(OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/irep_ids.h
    COMMAND irep_ids_convert header < ${CMAKE_CURRENT_SOURCE_DIR}/irep_ids.txt > ${CMAKE_CURRENT_BINARY_DIR}/irep_ids.h
)

add_custom_command(OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/irep_ids.inc
    COMMAND irep_ids_convert table < ${CMAKE_CURRENT_SOURCE_DIR}/irep_ids.txt > ${CMAKE_CURRENT_BINARY_DIR}/irep_ids.inc
)

file(GLOB_RECURSE sources "*.cpp")

add_library(util 
    ${sources}
    ${CMAKE_CURRENT_BINARY_DIR}/irep_ids.h
    ${CMAKE_CURRENT_BINARY_DIR}/irep_ids.inc
)

generic_includes(util)

target_link_libraries(util big-int)
