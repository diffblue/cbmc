/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INSTRUMENT_LITERALS_H
#define CPROVER_CEGIS_INSTRUMENT_LITERALS_H

#include <util/cprover_prefix.h>

#define CEGIS_INSTRUCTION_TYPE_NAME "tag-__CPROVER_cegis_instructiont"
#define CEGIS_OPS "__CPROVER_cegis_OPS"
#define CEGIS_EXECUTE "__CPROVER_danger_execute"
#define CEGIS_RESULT_OPS "__CPROVER_cegis_RESULT_OPS"
#define CEGIS_MODULE "<builtin-library-cegis>"
#define CEGIS_PREFIX CPROVER_PREFIX "cegis_"
#define CEGIS_TMP_PREFIX CEGIS_PREFIX "tmp_"
#define CEGIS_PRIME_SUFFIX "_prime"
#define CEGIS_CONSTANT_PREFIX "CEGIS_CONSTANT_"
#define CEGIS_FITNESS_TEST_FUNC "__CPROVER_cegis_test_fitness"
#define CPROVER_INIT CPROVER_PREFIX "initialize"
#define CONSTRAINT_CALLER_NAME CEGIS_PREFIX "constraint_caller"
#define CONSTRAINT_CALLER CONSTRAINT_CALLER_NAME ":()V"
#define CONSTRAINT_CALLER_ID "java::" CONSTRAINT_CALLER

#endif // CPROVER_CEGIS_INSTRUMENT_LITERALS_H
