add_subdirectory(regression)
add_subdirectory(src)
add_subdirectory(unit)

add_custom_target(java-models-library ALL
    COMMAND mvn --quiet -Dmaven.test.skip=true package
    COMMAND cp target/core-models.jar ${CMAKE_CURRENT_SOURCE_DIR}/src/java_bytecode/library/
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/lib/java-models-library
)

set_target_properties(
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

    PROPERTIES
    CXX_STANDARD ${CBMC_CXX_STANDARD}
    CXX_STANDARD_REQUIRED ${CBMC_CXX_STANDARD_REQUIRED}
    XCODE_ATTRIBUTE_CODE_SIGN_IDENTITY ${CBMC_XCODE_ATTRIBUTE_CODE_SIGN_IDENTITY}
)
