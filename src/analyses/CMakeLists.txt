file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(analyses ${sources})

generic_includes(analyses)

if(CMAKE_USE_CUDD)
    target_include_directories(analyses PUBLIC ${CUDD_INCLUDE}/cudd/)
endif()

target_link_libraries(analyses util pointer-analysis solvers)
