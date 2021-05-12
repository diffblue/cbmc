add_subdirectory(regression)
add_subdirectory(src)
add_subdirectory(unit)

cprover_default_properties(
    java_bytecode
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

# java models library
find_program(MAVEN_PROGRAM mvn REQUIRED)

file(GLOB_RECURSE java_models_sources "lib/java-models-library/src/*.java")

add_custom_command(OUTPUT "${CMAKE_CURRENT_SOURCE_DIR}/lib/java-models-library/target/core-models.jar"
    COMMAND ${MAVEN_PROGRAM} --quiet -Dmaven.test.skip=true package
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/lib/java-models-library
    DEPENDS ${java_models_sources}
)

add_custom_target(java-models-library ALL
    DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/lib/java-models-library/target/core-models.jar"
)

install(
  FILES
    "${CMAKE_CURRENT_SOURCE_DIR}/lib/java-models-library/target/core-models.jar"
    "${CMAKE_CURRENT_SOURCE_DIR}/lib/java-models-library/target/cprover-api.jar"
  DESTINATION ${CMAKE_INSTALL_LIBDIR}
)
if(NOT WIN32)
  install(
    DIRECTORY ${CMAKE_SOURCE_DIR}/doc/man/
    DESTINATION ${CMAKE_INSTALL_MANDIR}/man1
    FILES_MATCHING
    PATTERN "j*")
endif()
