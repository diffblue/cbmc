project(JBMC)

#   Set the public include locations for a target.
macro(generic_includes name)
    target_include_directories(${name}
        PUBLIC
        ${JBMC_BINARY_DIR}
        ${JBMC_SOURCE_DIR}
        ${CBMC_BINARY_DIR}
        ${CBMC_SOURCE_DIR}
        ${CMAKE_CURRENT_BINARY_DIR}
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CUDD_INCLUDE}
    )
endmacro(generic_includes)

add_subdirectory(miniz)
add_subdirectory(java_bytecode)
add_subdirectory(jbmc)
add_subdirectory(janalyzer)
add_subdirectory(jdiff)
