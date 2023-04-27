# Scan for all source files in the current or child directories
file(GLOB_RECURSE sources "*.cpp")
# Scan for all header files in the current or child directories (necessary to install them later)
file(GLOB_RECURSE headers "*.h")

add_library(options-lib OBJECT
    ${sources}
)

# Adding util as include dependency so the .cpp files may use header only
# libraries such as `optional.h`.
target_include_directories(options-lib PRIVATE "${CBMC_SOURCE_DIR}/util"
                                               "${CBMC_SOURCE_DIR}")

# Set the properties of `options-lib`.  Mainly the public headers to be installed
set_target_properties(options-lib
        PROPERTIES
        SOVERSION "${CMAKE_PROJECT_VERSION}"
        PUBLIC_HEADER "${headers}"
        )

# Install only the headers `include` as the library is "squashed" into
# `libcprover-cpp`.
install(TARGETS         options-lib
        RUNTIME   DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}/cprover/options"
                        COMPONENT lib
        )
