/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com,
        CM Wintersteiger

\*******************************************************************/


#ifndef CPROVER_SOLVERS_QBF_QBF_CORE_H
#define CPROVER_SOLVERS_QBF_QBF_CORE_H

#ifdef HAVE_QBF_CORE
#define QBF_CORE_SKIZZO
#else
#define QBF_CORE_NONE
#endif

#ifdef QBF_CORE_SQUOLEM

#include "qbf_squolem_core.h"
using qbf_coret = qbf_squolem_coret;

#else
#ifdef QBF_CORE_SKIZZO

#include "qbf_skizzo_core.h"
using qbf_coret = qbf_skizzo_coret;

#else
#ifdef QBF_CORE_BDD

#include "qbf_bdd_core.h"
using qbf_coret = qbf_bdd_coret;

#else

#error NO QBF SOLVER WITH CORE EXTRACTOR
#endif
#endif
#endif

#endif // CPROVER_SOLVERS_QBF_QBF_CORE_H
