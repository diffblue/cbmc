find_package(Java REQUIRED)
include(UseJava)
set(CMAKE_JAVA_COMPILE_FLAGS -sourcepath "src" -d "classes" -XDignore.symbol.file)
file(GLOB_RECURSE java_sources "*.java")
set(JAR_NAME "core-models")
add_jar(${JAR_NAME} ${java_sources})
get_filename_component(CORE_MODELS_JAR "core-models.jar" REALPATH BASE_DIR ${CMAKE_CURRENT_SOURCE_DIR})
get_filename_component(JAVA_CORE_MODELS_INC "java_core_models.inc" REALPATH BASE_DIR ${CMAKE_CURRENT_SOURCE_DIR})
file(GLOB_RECURSE jars "*.jar")
add_executable(java-converter converter.cpp)

add_custom_target(core_models_files)
add_dependencies(core_models_files ${JAR_NAME})
add_custom_command(TARGET core_models_files
                   PRE_BUILD
                   COMMAND java-converter JAVA_CORE_MODELS core-models.jar > ${JAVA_CORE_MODELS_INC}
                   )

set_source_files_properties("java_core_models.inc" GENERATED)
