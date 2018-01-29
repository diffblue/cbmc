get_filename_component(JAVA_CORE_MODELS_INC "library/java_core_models.inc" REALPATH BASE_DIR ${CMAKE_CURRENT_SOURCE_DIR})
set_source_files_properties("library/java_core_models.inc" GENERATED)

file(GLOB sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
add_subdirectory(library)

add_library(java_bytecode ${sources} ${headers} )
add_dependencies(java_bytecode core_models_files)
target_sources(java_bytecode PUBLIC ${sources} ${headers})

generic_includes(java_bytecode)

target_link_libraries(java_bytecode util goto-programs miniz json)
