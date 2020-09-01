set(CPACK_PACKAGE_NAME "cbmc")
set(CPACK_PACKAGE_VENDOR "Diffblue Ltd.")
set(CPACK_PACKAGE_CONTACT "Diffblue open source team <info@diffblue.com>")
set(CPACK_PACKAGE_DESCRIPTION_SUMMARY "CBMC is a Bounded Model Checker for C and C++ programs")
set(CPACK_PACKAGE_DESCRIPTION
"CBMC generates traces that demonstrate how an assertion can be violated,
or proves that the assertion cannot be violated within a given number
of loop iterations.")

set(CPACK_PACKAGE_VERSION_MAJOR ${PROJECT_VERSION_MAJOR})
set(CPACK_PACKAGE_VERSION_MINOR ${PROJECT_VERSION_MINOR})
set(CPACK_PACKAGE_VERSION_PATCH ${PROJECT_VERSION_PATCH})

# This should always be set, just isn’t by default for awkward backward compatibility reasons
set(CPACK_VERBATIM_VARIABLES YES)

set(CPACK_RESOURCE_FILE_LICENSE "${CMAKE_CURRENT_SOURCE_DIR}/LICENSE")
set(CPACK_PACKAGE_RESOURCE_FILE_README "${CMAKE_CURRENT_SOURCE_DIR}/README.md")

# Automatically find dependencies for shared libraries
set(CPACK_DEBIAN_PACKAGE_SHLIBDEPS YES)

# In addition, we depend on gcc for preprocessing
set(CPACK_DEBIAN_PACKAGE_DEPENDS gcc)

# TODO packages for other platforms
if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
  set(CPACK_GENERATOR TGZ DEB)
endif()

# Source package support
set(CPACK_SOURCE_GENERATOR TGZ)
set(CPACK_SOURCE_IGNORE_FILES
        /.git*
        /*build*
        /*.yml
        /AccessingCodebuildLogs.md
        /gcloud-travis-cbmc.json.enc
        )

# Support for generator specific configuration
set(CPACK_PROJECT_CONFIG_FILE "${CMAKE_CURRENT_SOURCE_DIR}/cmake/CPackGeneratorConfig.cmake")

# Yes, this has to go at the bottom,
# otherwise it can’t take into account
# all the variables we set above!
include(CPack)
