add_library(miniz
    ${CBMC_SOURCE_DIR}/3p/miniz-3.0.2/miniz.cpp
    ${CBMC_SOURCE_DIR}/3p/miniz-3.0.2/miniz.h
)

generic_includes(miniz)

target_include_directories(miniz
    PUBLIC
    ${CBMC_SOURCE_DIR}/3p
)

target_link_libraries(miniz)
