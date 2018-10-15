add_subdirectory(regression)
add_subdirectory(src)
add_subdirectory(unit)

add_custom_target(java-models-library ALL
    COMMAND mvn --quiet package
    COMMAND cp target/core-models.jar ${CMAKE_CURRENT_SOURCE_DIR}/src/java_bytecode/library/
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/lib/java-models-library
)
