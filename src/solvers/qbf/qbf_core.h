/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com,
        CM Wintersteiger

\*******************************************************************/

#ifndef CPROVER_QBFCHECK_CORE_H
#define CPROVER_QBFCHECK_CORE_H

#ifdef HAVE_QBF_CORE
#define QBF_CORE_SKIZZO
#else
#define QBF_CORE_NONE
#endif

#ifdef QBF_CORE_SQUOLEM

#include "qbf_squolem_core.h"
typedef qbf_squolem_coret qbf_coret;

#else
#ifdef QBF_CORE_SKIZZO

#include "qbf_skizzo_core.h"
typedef qbf_skizzo_coret qbf_coret;

#else
#ifdef QBF_CORE_BDD

#include "qbf_bdd_core.h"
typedef qbf_bdd_coret qbf_coret;

#else

#error NO QBF SOLVER WITH CORE EXTRACTOR
#endif
#endif
#endif

#endif
