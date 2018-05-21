find_package(Java REQUIRED)
include(UseJava)
set(CMAKE_JAVA_COMPILE_FLAGS -sourcepath "src" -d "classes" -XDignore.symbol.file)

# create a target for the executable performing the .jar -> .inc conversion
add_executable(java-converter converter.cpp)

# create a target 'core-models.jar' that depends on all .java files in src/
file(GLOB_RECURSE java_sources "src/*.java")
add_jar("core-models" ${java_sources})

# define a cmake variable with the full path of the .inc file
set(JAVA_CORE_MODELS_INC "${CMAKE_CURRENT_BINARY_DIR}/java_core_models.inc")

# define a rule telling cmake how to generate the file ${JAVA_CORE_MODELS_INC} from
# the .jar file by running the java-converter; the output file depends on the
# .jar file but also on the converter (!)
add_custom_command(OUTPUT ${JAVA_CORE_MODELS_INC}
    COMMAND java-converter "JAVA_CORE_MODELS" "core-models.jar" > ${JAVA_CORE_MODELS_INC}
    DEPENDS "core-models.jar" java-converter)

# create a target 'core-models-inc' that depends on the .inc file
add_custom_target(java-core-models-inc
    DEPENDS ${JAVA_CORE_MODELS_INC})
