#   We may use one of several different solver libraries.
#   The following files wrap the chosen solver library.
#   We remove them all from the solver-library sources list, and then add the
#   ones we actually need back in.
set(chaff_source
    ${CMAKE_CURRENT_SOURCE_DIR}/sat/satcheck_zchaff.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/sat/satcheck_zcore.cpp
)
set(minisat_source
    ${CMAKE_CURRENT_SOURCE_DIR}/sat/satcheck_minisat.cpp
)
set(minisat2_source
    ${CMAKE_CURRENT_SOURCE_DIR}/sat/satcheck_minisat2.cpp
)
set(glucose_source
    ${CMAKE_CURRENT_SOURCE_DIR}/sat/satcheck_glucose.cpp
)
set(smvsat_source
    ${CMAKE_CURRENT_SOURCE_DIR}/sat/satcheck_smvsat.cpp
)
set(squolem2_source
    ${CMAKE_CURRENT_SOURCE_DIR}/qbf/qbf_squolem.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/qbf/qbf_squolem_core.cpp
)
set(cudd_source
    ${CMAKE_CURRENT_SOURCE_DIR}/qbf/qbf_bdd_core.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/qbf/qbf_skizzo_core.cpp
)
set(precosat_source
    ${CMAKE_CURRENT_SOURCE_DIR}/sat/satcheck_precosat.cpp
)
set(picosat_source
    ${CMAKE_CURRENT_SOURCE_DIR}/sat/satcheck_picosat.cpp
)
set(lingeling_source
    ${CMAKE_CURRENT_SOURCE_DIR}/sat/satcheck_lingeling.cpp
)
set(booleforce_source
    ${CMAKE_CURRENT_SOURCE_DIR}/sat/satcheck_booleforce.cpp
)
set(minibdd_source
    ${CMAKE_CURRENT_SOURCE_DIR}/miniBDD/example.cpp
)
set(limmat_source
    ${CMAKE_CURRENT_SOURCE_DIR}/sat/satcheck_limmat.cpp
)

file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${chaff_source}
    ${minisat_source}
    ${minisat2_source}
    ${glucose_source}
    ${smvsat_source}
    ${squolem2_source}
    ${cudd_source}
    ${precosat_source}
    ${picosat_source}
    ${lingeling_source}
    ${booleforce_source}
    ${minibdd_source}
    ${limmat_source}
)

add_library(solvers ${sources})

include("${CBMC_SOURCE_DIR}/../cmake/DownloadProject.cmake")

if("${sat_impl}" STREQUAL "minisat2")
    message(STATUS "Building solvers with minisat2")

    download_project(PROJ minisat2
        URL http://ftp.debian.org/debian/pool/main/m/minisat2/minisat2_2.2.1.orig.tar.gz
        PATCH_COMMAND patch -p1 -i ${CBMC_SOURCE_DIR}/../scripts/minisat-2.2.1-patch
        COMMAND cmake -E copy ${CBMC_SOURCE_DIR}/../scripts/minisat2_CMakeLists.txt CMakeLists.txt
    )

    add_subdirectory(${minisat2_SOURCE_DIR} ${minisat2_BINARY_DIR})

    target_compile_definitions(solvers PUBLIC
        SATCHECK_MINISAT2 HAVE_MINISAT2 __STDC_FORMAT_MACROS __STDC_LIMIT_MACROS
    )

    target_sources(solvers PRIVATE ${minisat2_source})

    target_link_libraries(solvers minisat2-condensed)
elseif("${sat_impl}" STREQUAL "glucose")
    message(STATUS "Building solvers with glucose")

    download_project(PROJ glucose
        URL http://www.labri.fr/perso/lsimon/downloads/softwares/glucose-syrup.tgz
        PATCH_COMMAND patch -p1 -i ${CBMC_SOURCE_DIR}/../scripts/glucose-syrup-patch
        COMMAND cmake -E copy ${CBMC_SOURCE_DIR}/../scripts/glucose_CMakeLists.txt CMakeLists.txt
    )

    add_subdirectory(${glucose_SOURCE_DIR} ${glucose_BINARY_DIR})

    target_compile_definitions(solvers PUBLIC
        SATCHECK_GLUCOSE HAVE_GLUCOSE __STDC_FORMAT_MACROS __STDC_LIMIT_MACROS
    )

    target_sources(solvers PRIVATE ${glucose_source})

    target_link_libraries(solvers glucose-condensed)
endif()

target_link_libraries(solvers java_bytecode util)

generic_includes(solvers)
