set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED true)

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
set(squolem2_source
    ${CMAKE_CURRENT_SOURCE_DIR}/qbf/qbf_squolem.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/qbf/qbf_squolem_core.cpp
)
set(cudd_source
    ${CMAKE_CURRENT_SOURCE_DIR}/qbf/qbf_bdd_core.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/qbf/qbf_skizzo_core.cpp
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
    ${CMAKE_CURRENT_SOURCE_DIR}/bdd/miniBDD/example.cpp
)
set(ipasir_source
    ${CMAKE_CURRENT_SOURCE_DIR}/sat/satcheck_ipasir.cpp
)


file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${chaff_source}
    ${minisat_source}
    ${minisat2_source}
    ${glucose_source}
    ${squolem2_source}
    ${cudd_source}
    ${picosat_source}
    ${lingeling_source}
    ${booleforce_source}
    ${minibdd_source}
    # ${ipasir_source}
)

add_library(solvers ${sources})

include("${CBMC_SOURCE_DIR}/../cmake/DownloadProject.cmake")

if("${sat_impl}" STREQUAL "minisat2")
    message(STATUS "Building solvers with minisat2")

    # once we upgrade to CMake 3.7 or higher we can specify multiple URLs as a
    # fall-back in case the first URL fails (the Makefile-based build retries up
    # to 2 times)
    download_project(PROJ minisat2
        URL http://ftp.debian.org/debian/pool/main/m/minisat2/minisat2_2.2.1.orig.tar.gz
        PATCH_COMMAND patch -p1 -i ${CBMC_SOURCE_DIR}/../scripts/minisat-2.2.1-patch
        COMMAND cmake -E copy ${CBMC_SOURCE_DIR}/../scripts/minisat2_CMakeLists.txt CMakeLists.txt
        URL_MD5 27faa19ee0508660bd6fb7f894646d42
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
        URL_MD5 b6f040a6c28f011f3be994663338f548
    )

    add_subdirectory(${glucose_SOURCE_DIR} ${glucose_BINARY_DIR})

    target_compile_definitions(solvers PUBLIC
        SATCHECK_GLUCOSE HAVE_GLUCOSE __STDC_FORMAT_MACROS __STDC_LIMIT_MACROS
    )

    target_sources(solvers PRIVATE ${glucose_source})

    target_link_libraries(solvers glucose-condensed)
elseif("${sat_impl}" STREQUAL "cadical")
    message(STATUS "Building solvers with cadical")

    download_project(PROJ cadical
        URL https://github.com/arminbiere/cadical/archive/rel-1.3.0.tar.gz
        PATCH_COMMAND true
        COMMAND CXX=${CMAKE_CXX_COMPILER} ./configure -O3 -s -j
        URL_MD5 5bd15d1e198d2e904a8af8b7873dd341
    )

    message(STATUS "Building CaDiCaL")
    execute_process(COMMAND make WORKING_DIRECTORY ${cadical_SOURCE_DIR})

    target_compile_definitions(solvers PUBLIC
        SATCHECK_CADICAL HAVE_CADICAL
    )

    add_library(cadical STATIC IMPORTED)

    set_target_properties(
        cadical
        PROPERTIES IMPORTED_LOCATION ${cadical_SOURCE_DIR}/build/libcadical.a
    )

    target_include_directories(solvers
      PUBLIC
      ${cadical_SOURCE_DIR}/src
    )

    target_link_libraries(solvers cadical)
elseif("${sat_impl}" STREQUAL "ipasir-cadical")
    message(STATUS "Building with IPASIR solver linking against: CaDiCaL")

    download_project(PROJ cadical
        URL https://github.com/arminbiere/cadical/archive/rel-1.4.0.tar.gz
        PATCH_COMMAND true
        COMMAND ./configure CXX=g++
        URL_MD5 9bad586a82995a1d95d1197d445a353a
    )

    message(STATUS "Building CaDiCaL")
    execute_process(COMMAND make WORKING_DIRECTORY ${cadical_SOURCE_DIR})

    target_compile_definitions(solvers PUBLIC
        SATCHECK_IPASIR HAVE_IPASIR IPASIR=${cadical_SOURCE_DIR}/src
    )

    add_library(cadical_ipasir STATIC IMPORTED)
    set_property(TARGET cadical_ipasir
        PROPERTY IMPORTED_LOCATION ${cadical_SOURCE_DIR}/build/libcadical.a
    )

    target_include_directories(solvers
        PUBLIC
        ${cadical_SOURCE_DIR}/src
    )
    target_link_libraries(solvers cadical_ipasir)
elseif("${sat_impl}" STREQUAL "ipasir-custom")
    message(STATUS "Building with IPASIR solver linking: custom solver provided")

    if (NOT DEFINED IPASIR)
        message(FATAL_ERROR
          "IPASIR solver source code not provided. Please use -DIPASIR=<location> "
          "with <location> being the path to the IPASIR solver source code."
        )
    endif()

    if (NOT DEFINED IPASIR_LIB)
        message(FATAL_ERROR
            "IPASIR solver library not provided. Please use -DIPASIR_LIB=<location> "
            "with <location> being the path to the IPASIR solver precompiled static "
            "library."
        )
    endif()

    target_compile_definitions(solvers PUBLIC
        SATCHECK_IPASIR HAVE_IPASIR IPASIR=${IPASIR}
    )

    add_library(ipasir_custom STATIC IMPORTED)
    set_property(TARGET ipasir_custom
        PROPERTY IMPORTED_LOCATION ${IPASIR_LIB}
    )

    target_include_directories(solvers
        PUBLIC
        ${IPASIR}
    )
    target_link_libraries(solvers ipasir_custom pthread)
endif()

if(CMAKE_USE_CUDD)
    target_link_libraries(solvers util cudd-cplusplus cudd)
    target_include_directories(solvers
        PUBLIC
        ${CUDD_INCLUDE}/cudd/
    )
else()
    target_link_libraries(solvers util)
endif()

# Executable
add_executable(smt2_solver smt2/smt2_solver.cpp)
target_link_libraries(smt2_solver solvers)

generic_includes(solvers)
