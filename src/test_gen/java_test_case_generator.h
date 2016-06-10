/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef JAVA_TEST_CASE_GENERATOR_H_
#define JAVA_TEST_CASE_GENERATOR_H_

#define TEST_CASE_SUCCESS 0
#define TEST_CASE_FAIL 1
#define TEST_CASE_ERROR 10

/**
 * @brief
 *
 * @details
 *
 * @param options
 * @param st
 * @param gf
 * @param bmc
 */
int generate_java_test_case(
    const class optionst &options,
    const class symbol_tablet &st,
    const class goto_functionst &gf,
    class bmct &bmc);

#endif /* JAVA_TEST_CASE_GENERATOR_H_ */
