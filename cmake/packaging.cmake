set(CPACK_PACKAGE_NAME "cbmc")
set(CPACK_PACKAGE_VENDOR "Diffblue Ltd.")
set(CPACK_PACKAGE_CONTACT "Diffblue Open Source Team <cbmc@diffblue.com>")
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

# The WiX package generator expects licenses to end in .txt or .rtf...
file(COPY "${CMAKE_CURRENT_SOURCE_DIR}/LICENSE" DESTINATION "${CMAKE_CURRENT_BINARY_DIR}")
file(RENAME "${CMAKE_CURRENT_BINARY_DIR}/LICENSE" "${CMAKE_CURRENT_BINARY_DIR}/LICENSE.txt")

set(CPACK_RESOURCE_FILE_LICENSE "${CMAKE_CURRENT_BINARY_DIR}/LICENSE.txt")
set(CPACK_PACKAGE_RESOURCE_FILE_README "${CMAKE_CURRENT_SOURCE_DIR}/README.md")

# Automatically find dependencies for shared libraries
set(CPACK_DEBIAN_PACKAGE_SHLIBDEPS YES)

# In addition, we depend on gcc for preprocessing and bash-completion to make
# CBMC's bash completion work
set(CPACK_DEBIAN_PACKAGE_DEPENDS "gcc, bash-completion")

# Enable debug output so that we can see the dependencies being generated in the
# logs
set(CPACK_DEBIAN_PACKAGE_DEBUG YES)

# For windows we need to set up product and update GUID
# See: https://docs.microsoft.com/en-us/windows/win32/msi/productcode
# and  https://docs.microsoft.com/en-us/windows/win32/msi/upgradecode
# confusingly, the "product" GUID here is the one that changes between releases,
# the upgrade one is the one that stays the same. CMake takes care of setting these,
# but we want to fix the upgrade GUID to a specific value so new installs override
# old ones.
set(NIL_UUID "00000000-0000-0000-0000-000000000000")
string(UUID CPACK_WIX_UPGRADE_GUID
  NAMESPACE ${NIL_UUID}
  NAME "cprover-cbmc"
  TYPE SHA1
  UPPER)


# This is AFAICT only used for windows installers.
# Basically the package-specific part of the install directory,
# e.g. C:\Program Files\${CPACK_PACKAGE_INSTALL_DIRECTORY}.
# The default here includes the version number which we don't want,
# because upgrades will overwrite the files here so we could be in the
# odd situation where C:\Program Files\cbmc-5.12.6\bin\cbmc --version
# gives you back "5.16.1" because 5.12.6 just happened to be the first
# installed version.
set(CPACK_PACKAGE_INSTALL_DIRECTORY "cbmc")


# TODO packages for other platforms
if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
  set(CPACK_GENERATOR TGZ DEB)
elseif(WIN32)
  # Note: We don't ship VC redistributables with
  # the windows installer; We assume these are likely
  # already present on a developer machine, and if not
  # can easily be installed separately via vcredist.exe
  set(CPACK_GENERATOR ZIP WIX)
endif()

# Yes, this has to go at the bottom,
# otherwise it can’t take into account
# all the variables we set above!
include(CPack)
