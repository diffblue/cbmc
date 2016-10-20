/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_LITERALS_H_
#define CEGIS_LITERALS_H_

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

#endif /* CEGIS_LITERALS_H_ */
