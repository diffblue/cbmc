message(STATUS "Downloading java-models-library...")
include("${CBMC_SOURCE_DIR}/../cmake/DownloadProject.cmake")

#  Note: 'PATCH_COMMAND' is being used instead of 'COMMAND' as
# 'download_project' does not work as expected if called without
# 'PATCH_COMMAND'.
download_project(PROJ java_models_library
    URL https://github.com/diffblue/java-models-library/archive/master.zip
    PATCH_COMMAND cmake -E copy_directory "${CMAKE_BINARY_DIR}/java_models_library-src/src"
      "${JBMC_SOURCE_DIR}/java_bytecode/library/src"
)

find_package(Java REQUIRED)
include(UseJava)

set(CMAKE_JAVA_COMPILE_FLAGS -sourcepath "src" -d "classes" -XDignore.symbol.file)

# create a target for the executable performing the .jar -> .inc conversion
add_executable(java-converter converter.cpp)

# create a target 'core-models.jar' that depends on all .java files in src/
file(GLOB_RECURSE java_sources "src/*.java")
add_jar("core-models" ${java_sources})

# copy 'core-models.jar' to '<PROJECT_ROOT>/jbmc/src/java_bytecode/library'.
# This is needed to deal with unit tests that make use of the core-models
# library. So that they can find the 'core-models.jar' in the same place as
# if the project had been compiled with 'make'.
add_custom_command(TARGET core-models
                   POST_BUILD
                   COMMAND ${CMAKE_COMMAND} -E copy "core-models.jar" ${PROJECT_SOURCE_DIR}/java_bytecode/library
                  )
