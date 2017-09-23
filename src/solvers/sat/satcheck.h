/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SAT_SATCHECK_H
#define CPROVER_SOLVERS_SAT_SATCHECK_H

// this picks the "default" SAT solver

// #define SATCHECK_ZCHAFF
// #define SATCHECK_MINISAT1
// #define SATCHECK_MINISAT2
// #define SATCHECK_GLUCOSE
// #define SATCHECK_BOOLEFORCE
// #define SATCHECK_PRECOSAT
// #define SATCHECK_PICOSAT
// #define SATCHECK_LINGELING

#if defined SATCHECK_ZCHAFF

#include "satcheck_zchaff.h"

using satcheckt = satcheck_zchafft;
using satcheck_no_simplifiert = satcheck_zchafft;

#elif defined SATCHECK_BOOLEFORCE

#include "satcheck_booleforce.h"

using satcheckt = satcheck_booleforcet;
using satcheck_no_simplifiert = satcheck_booleforcet;

#elif defined SATCHECK_MINISAT1

#include "satcheck_minisat.h"

using satcheckt = satcheck_minisat1t;
using satcheck_no_simplifiert = satcheck_minisat1t;

#elif defined SATCHECK_MINISAT2

#include "satcheck_minisat2.h"

using satcheckt = satcheck_minisat_simplifiert;
using satcheck_no_simplifiert = satcheck_minisat_no_simplifiert;

#elif defined SATCHECK_PRECOSAT

#include "satcheck_precosat.h"

using satcheckt = satcheck_precosatt;
using satcheck_no_simplifiert = satcheck_precosatt;

#elif defined SATCHECK_PICOSAT

#include "satcheck_picosat.h"

using satcheckt = satcheck_picosatt;
using satcheck_no_simplifiert = satcheck_picosatt;

#elif defined SATCHECK_LINGELING

#include "satcheck_lingeling.h"

using satcheckt = satcheck_lingelingt;
using satcheck_no_simplifiert = satcheck_lingelingt;

#elif defined SATCHECK_GLUCOSE

#include "satcheck_glucose.h"

using satcheckt = satcheck_glucose_simplifiert;
using satcheck_no_simplifiert = satcheck_glucose_no_simplifiert;

#endif

#endif // CPROVER_SOLVERS_SAT_SATCHECK_H
