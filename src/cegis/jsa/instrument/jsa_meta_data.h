/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/cprover_prefix.h>
#include <util/source_location.h>

#ifndef CPROVER_CEGIS_JSA_INSTRUMENT_JSA_META_DATA_H
#define CPROVER_CEGIS_JSA_INSTRUMENT_JSA_META_DATA_H

#define JSA_MODULE "<builtin-library-jsa>"
#define JSA_PREFIX CPROVER_PREFIX "jsa_"
#define JSA_BASE_CASE JSA_PREFIX "base_case"
#define JSA_IND_ASSUME JSA_PREFIX "inductive_assume"
#define JSA_IND_STEP JSA_PREFIX "inductive_step"
#define JSA_PROP_ENTAIL JSA_PREFIX "property_entailment"
#define JSA_TMP_PREFIX JSA_PREFIX "tmp_"
#define JSA_LAMBDA_OP JSA_PREFIX "lambda_op"
#define JSA_CONSTANT_PREFIX CPROVER_PREFIX "jsa_constant_"
#define JSA_QUERY JSA_PREFIX "query"
#define JSA_QUERY_SZ JSA_QUERY "_size"
#define JSA_INV JSA_PREFIX "invariant"
#define JSA_INV_SZ JSA_INV "_size"
#define JSA_POST JSA_PREFIX "postcondition"
#define JSA_POST_SZ JSA_POST "_size"
#define JSA_QUERIED_HEAP JSA_PREFIX "queried_heap"
#define JSA_ORG_HEAP JSA_PREFIX "org_heap"
#define JSA_HEAP_TAG "tag-" JSA_PREFIX "abstract_heap"
#define JSA_PRED_PREFIX JSA_PREFIX "predicate_"
#define JSA_SIZE_SUFFIX "_size"
#define JSA_INV_EXEC JSA_PREFIX "invariant_execute"
#define JSA_INV_VERIFY_EXEC JSA_PREFIX "verify_invariant_execute"
#define JSA_QUERY_EXEC JSA_PREFIX "query_execute"
#define JSA_STREAM_OP JSA_PREFIX "stream_op"
#define JSA_PRED_EXEC JSA_PREFIX "execute_pred"
#define JSA_STATIC_META_VAR_PREFIX CPROVER_PREFIX "JSA_"
#define JSA_ASSUME_VALID_PRED JSA_PREFIX "assume_valid_pred"
#define JSA_PRED_RES_OPS "__CPROVER_JSA_PRED_RESULT_OPS"

/**
 * @brief
 *
 * @details
 *
 * @param type
 *
 * @return
 */
bool is_jsa_heap(const class typet &type);

/**
 * @brief
 *
 * @details
 *
 * @param id
 *
 * @return
 */
bool is_jsa_iterator(const irep_idt &id);

/**
 * @brief
 *
 * @details
 *
 * @param id
 *
 * @return
 */
bool is_jsa_list(const irep_idt &id);

/**
 * @brief
 *
 * @details
 *
 * @return
 */
source_locationt jsa_builtin_source_location();

/**
 * @brief
 *
 * @details
 *
 * @param symbol
 *
 * @return
 */
bool is_jsa_const(const class symbol_exprt &symbol);

#endif // CPROVER_CEGIS_JSA_INSTRUMENT_JSA_META_DATA_H
