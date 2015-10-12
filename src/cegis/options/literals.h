/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_LITERALS_H_
#define CEGIS_LITERALS_H_

/**
 * @brief Prefix for synthesised programs.
 *
 * @details Prefix for variable names of synthesised programs. All these
 * variables are arrays of instructions.
 */
#define SYNTHESIS_PROG "__CPROVER_synthesis_program_"

/**
 * @brief Length of the program variable prefix.
 *
 * @details Introduced as explicit constant for convenience.
 */
#define SYNTHESIS_PROG_PREFIX_LEN 28

/**
 * @brief
 *
 * @details
 */
#define SYNTHESIS_MODULE "<builtin-library-synthesis>"

/**
 * @brief
 *
 * @details
 */
#define BUILTIN_MODULE "<built-in-additions>"

/**
 * @brief
 *
 * @details
 */
#define CPROVER_VARIABLE_PREFIX "__CPROVER_"

/**
 * @brief
 *
 * @details
 */
#define CPROVER_SYNTHESIS_ARG_PREFIX "__CPROVER_synthesis_arg_"

/**
 * @brief
 *
 * @details
 */
#define CPROVER_SYNTHESIS_PRIVATE_ARG_PREFIX "__CPROVER_synthesis_private_arg_"

/**
 * @brief
 *
 * @details
 */
#define CPROVER_SYNTHESIS_CONST_PREFIX "__CPROVER_synthesis_const_"

/**
 * @brief
 *
 * @details
 */
#define CPROVER_SYNTHESIS_TMPVAR_PREFIX "__CPROVER_synthesis_tmp_"

/**
 * @brief
 *
 * @details
 */
#define CPROVER_SYNTHESIS_WRITEONLY_PREFIX "__CPROVER_synthesis_writeonly_"

/**
 * @brief
 *
 * @details
 */
#define CPROVER_SYNTHESIS_SKOLEM_PREFIX "__CPROVER_synthesis_skolem_"

/**
 * @brief
 *
 * @details
 */
#define CPROVER_SYNTHESIS_RANKING_PREFIX "__CPROVER_synthesis_ranking_"

/**
 * @brief
 *
 * @details
 */
#define SYNTHESIS_INSTR_TYPE_SYMBOL_NAME "tag-__CPROVER_synthesis_instructiont"

/**
 * @brief
 *
 * @details
 */
#define SYNTHESIS_EXECUTE "__CPROVER_synthesis_execute"

/**
 * @brief Source location of generated constants.
 *
 * @details Used as source location for generated variables and their initialisation.
 * Function doesn't actually exist.
 */
#define SYNTHESIS_INIT "__CPROVER_synthesis_initialize"

#endif /* CEGIS_LITERALS_H_ */
