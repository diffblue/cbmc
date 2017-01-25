/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_VALUE_JSA_GENETIC_SYNTHESIS_H
#define CPROVER_CEGIS_JSA_VALUE_JSA_GENETIC_SYNTHESIS_H

#define __CPROVER_JSA_MAX_CONCRETE_NODES 3u
#define __CPROVER_JSA_MAX_ABSTRACT_NODES 0u
#define __CPROVER_JSA_MAX_LISTS 2u
#define __CPROVER_JSA_MAX_NODES_PER_CE_LIST 1u
#define __CPROVER_JSA_MAX_ITERATORS 2u

#define __CPROVER_JSA_MAX_QUERY_SIZE 4u
#define __CPROVER_JSA_MAX_PRED_SIZE 3u
#define __CPROVER_JSA_NUM_PRED_OPS 7u
#define __CPROVER_JSA_NUM_PRED_RESULT_OPS 3u

#define JSA_GENETIC_SYNTHESIS_H_

typedef bool _Bool;

#include <ansi-c/library/jsa.h>

#endif // CPROVER_CEGIS_JSA_VALUE_JSA_GENETIC_SYNTHESIS_H
