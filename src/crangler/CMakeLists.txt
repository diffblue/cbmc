generic_flex(c)

# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/crangler_main.cpp
)

add_library(crangler-lib
    ${sources}
    ${FLEX_scanner_OUTPUTS}
)

generic_includes(crangler-lib)

target_link_libraries(crangler-lib
    big-int
    util
    json
)

# Executable
add_executable(crangler crangler_main.cpp)
target_link_libraries(crangler crangler-lib)

install(TARGETS crangler DESTINATION ${CMAKE_INSTALL_BINDIR})

# Man page
if(NOT WIN32)
  install(
    DIRECTORY ${CMAKE_SOURCE_DIR}/doc/man/
    DESTINATION ${CMAKE_INSTALL_MANDIR}/man1
    FILES_MATCHING PATTERN "crangler*")
endif()
