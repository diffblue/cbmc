file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(goto-symex ${sources})

generic_includes(goto-symex)

if(CMAKE_USE_CUDD)
    target_include_directories(goto-symex PUBLIC ${CUDD_INCLUDE}/cudd/)
endif()

target_link_libraries(goto-symex util)
