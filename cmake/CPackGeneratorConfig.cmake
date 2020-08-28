# This is run once per generator, which means that generator specific logic can
# go here.

message(STATUS "Configuring for generator ${CPACK_GENERATOR} and TOPLEVEL_TAG ${CPACK_TOPLEVEL_TAG}")

if("${CPACK_TOPLEVEL_TAG}" STREQUAL "Linux-Source")
  message(STATUS "Adding build time dependencies")
  # Python for various scripts including testing and linting.
  set(CPACK_DEBIAN_PACKAGE_DEPENDS "${CPACK_DEBIAN_PACKAGE_DEPENDS},python,python3")
  # Node for benchmark scripts
  set(CPACK_DEBIAN_PACKAGE_DEPENDS "${CPACK_DEBIAN_PACKAGE_DEPENDS},nodejs")
endif()
