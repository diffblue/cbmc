# Scan for all source files in the current or child directories
file(GLOB_RECURSE sources "*.cpp")
# Scan for all header files in the current or child directories (necessary to install them later)
file(GLOB_RECURSE headers "*.h")

# This step builds the API in the form of a statically linked library
add_library(cprover-api-cpp ${sources})

# Being a library we should include them privately, but for now fair enough
generic_includes(cprover-api-cpp)

# Add all the current and the installed `include` directories as a PUBLIC header location
target_include_directories(cprover-api-cpp PUBLIC
                           "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>"
                           "$<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}>"
                           "$<INSTALL_INTERFACE:include>")

# To create a full static API library we need to archive together the content of all the other
# module libraries we depend on.  To do this we will use the `ar` command to unpack the other module
# static libraries and append to the current library `.a` file.

# Get the dependency targets of the `solver` target (see `../solver/CMakeLists.txt`), so that they
# are merged to the final library too.  (such dependencies are not known statically as the selection
# of the SAT backend is left to the building user.
get_target_property(LIBRARY_DEPENDENCIES solvers LINK_LIBRARIES)

# Get all the dependency targets we know statically.
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

# Remove possible duplicate library targets
list(REMOVE_DUPLICATES LIBRARY_DEPENDENCIES)

# Add all the dependency targets as dependencies of `cprover-api-cpp`
target_link_libraries(cprover-api-cpp
                      PRIVATE
                      options-lib
                      ${LIBRARY_DEPENDENCIES})

# To be able to invoke `ar` on the dependencies we need the paths of the libraries `.a` files.
# Ths is done by using the cmake generator `$<TARGET_FILE:dependency>`, that in turn will be
# substituted with the absolute path of the `dependency` output file (a `.a` file in this case).
# Here we prepare a space-separated list of cmake generators that will resolved in  absolute paths.
set(DEPENDENCY_TARGETS "")
foreach(dep ${LIBRARY_DEPENDENCIES})
    list(APPEND DEPENDENCY_TARGETS "$<TARGET_FILE:${dep}>")
endforeach(dep LIBRARY_DEPENDENCIES)
string(REPLACE ";" " " DEPENDENCY_TARGETS "${DEPENDENCY_TARGETS}")

# To aggregate all the dependencies into a final `.a` file we add a custom pass after target
# `cprover-api-cpp` has been built where the `aggregate_dependencies.sh` script is run with the `ar`
# command, the destination library and the dependencies paths
add_custom_command(TARGET cprover-api-cpp POST_BUILD
                   COMMAND "${CMAKE_CURRENT_SOURCE_DIR}/add_dependencies.sh" "${CMAKE_AR}" "$<TARGET_FILE:cprover-api-cpp>" "${DEPENDENCY_TARGETS}"
                   WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}")

# Set the properties of `cprover-api-cpp`.  Mainly the output name `libcprover.<version>.a`, its
# version (CBMC version) and the list of public headers to be installed
set_target_properties(cprover-api-cpp
        PROPERTIES
        OUTPUT_NAME "cprover.${CMAKE_PROJECT_VERSION}" # libcprover.<version>.a
        SOVERSION "${CMAKE_PROJECT_VERSION}"
        PUBLIC_HEADER "${headers}"
        )

# Install the target as usual in `lib` the library and in `include/cprover` the public headers.
install(TARGETS         cprover-api-cpp
        ARCHIVE         DESTINATION "${CMAKE_INSTALL_LIBDIR}"
                        COMPONENT lib
        LIBRARY         DESTINATION "${CMAKE_INSTALL_LIBDIR}"
                        COMPONENT lib
        PUBLIC_HEADER   DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}/cprover"
                        COMPONENT lib
        )
