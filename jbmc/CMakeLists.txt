add_subdirectory(regression)
add_subdirectory(src)
add_subdirectory(unit)

add_custom_target(java-models-library ALL
    COMMAND mvn --quiet -Dmaven.test.skip=true package
    COMMAND cp target/core-models.jar ${CMAKE_CURRENT_SOURCE_DIR}/src/java_bytecode/library/
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/lib/java-models-library
)

cprover_default_properties(
    java_bytecode
    java-models-library
    jbmc
    jbmc-lib
    janalyzer
    janalyzer-lib
    jdiff
    jdiff-lib
    java-testing-utils
    java-unit
    miniz
)
