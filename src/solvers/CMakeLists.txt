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

file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
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

    # Some files just don't build
    ${CMAKE_CURRENT_SOURCE_DIR}/cvc/cvc_prop.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/dplib/dplib_prop.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/dplib/dplib_conv.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/dplib/dplib_dec.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/floatbv/float_approximation.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/sat/satcheck_limmat.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/smt1/smt1_prop.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/smt2/smt2_prop.cpp
)

add_library(solvers ${sources} ${headers})

if("${sat_impl}" STREQUAL "minisat2" AND TARGET minisat2-extern)
    target_sources(solvers PRIVATE ${minisat2_source})
    add_dependencies(solvers minisat2-extern)
    target_compile_definitions(solvers PUBLIC SATCHECK_MINISAT2 HAVE_MINISAT2 __STDC_FORMAT_MACROS __STDC_LIMIT_MACROS)
    target_link_libraries(solvers minisat2-condensed)
elseif("${sat_impl}" STREQUAL "glucose" AND TARGET glucose-extern)
    target_sources(solvers PRIVATE ${glucose_source})
    add_dependencies(solvers glucose-extern)
    target_compile_definitions(solvers PUBLIC SATCHECK_GLUCOSE HAVE_GLUCOSE __STDC_FORMAT_MACROS __STDC_LIMIT_MACROS)
    target_link_libraries(solvers glucose-condensed)
endif()

target_link_libraries(solvers util)

generic_includes(solvers)
