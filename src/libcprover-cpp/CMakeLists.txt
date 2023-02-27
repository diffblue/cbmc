file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")

# This step builds the API in the form of a statically linked library
add_library(cprover-api-cpp ${sources})

# Being a library we should include them privately, but for now fair enough
generic_includes(cprover-api-cpp)

target_include_directories(cprover-api-cpp PUBLIC
                           "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>"
                           "$<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}>"
                           "$<INSTALL_INTERFACE:include>")

get_target_property(LIBRARY_DEPENDENCIES solvers LINK_LIBRARIES)

list(APPEND
        LIBRARY_DEPENDENCIES
        "goto-programs"
        "util"
        "langapi"
        "ansi-c"
        "analyses"
        "goto-instrument-lib"
        "big-int"
        "linking"
        "goto-checker"
        "solvers"
        "assembler"
        "xml"
        "json"
        "json-symtab-language"
        "jsil"
        "statement-list"
        "goto-symex"
        "pointer-analysis"
        "cbmc-lib")

list(REMOVE_DUPLICATES LIBRARY_DEPENDENCIES)

target_link_libraries(cprover-api-cpp
                      PRIVATE
                      ${LIBRARY_DEPENDENCIES})

set(DEPENDENCY_TARGETS "")
foreach(dep ${LIBRARY_DEPENDENCIES})
    list(APPEND DEPENDENCY_TARGETS "$<TARGET_FILE:${dep}>")
endforeach(dep LIBRARY_DEPENDENCIES)

string(REPLACE ";" " " DEPENDENCY_TARGETS "${DEPENDENCY_TARGETS}")

add_custom_command(TARGET cprover-api-cpp POST_BUILD
                   COMMAND "${CMAKE_CURRENT_SOURCE_DIR}/add_dependencies.sh" "${CMAKE_AR}" "$<TARGET_FILE:cprover-api-cpp>" "${DEPENDENCY_TARGETS}"
                   WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}")

set_target_properties(cprover-api-cpp
        PROPERTIES
        OUTPUT_NAME "cprover.${CMAKE_PROJECT_VERSION}" # libcprover.<version>.a
        SOVERSION "${CMAKE_PROJECT_VERSION}"
        PUBLIC_HEADER "${headers}"
        )

install(TARGETS         cprover-api-cpp
        ARCHIVE         DESTINATION "${CMAKE_INSTALL_LIBDIR}"
                        COMPONENT lib
        LIBRARY         DESTINATION "${CMAKE_INSTALL_LIBDIR}"
                        COMPONENT lib
        PUBLIC_HEADER   DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}/cprover"
                        COMPONENT lib
        )
