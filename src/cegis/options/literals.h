/*******************************************************************
 Module:  Counterexample-Guided Inductive Synthesis

 Authors: Daniel Kroening, kroening@kroening.com
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
#define CPROVER_SYNTHESIS_VARIABLE_PREFIX "__CPROVER_synthesis_arg_"

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

#endif /* CEGIS_LITERALS_H_ */
