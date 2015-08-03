/*******************************************************************
 Module:  Counterexample-Guided Inductive Synthesis

 Authors: Daniel Kroening, kroening@kroening.com
 Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CEGIS_SYMEX_TEST_CASE_FACTORY_H_
#define CEGIS_SYMEX_TEST_CASE_FACTORY_H_

#include <util/expr.h>

/**
 * @brief
 *
 * @details
 */
class test_case_factoryt
{
  symbol_tablet &st;
  goto_functionst &gf;
  const cegis_optionst &options;
  source_location_factoryt &lfactory;
  const exprt &synthesis_property;
  size_t counterexample_count;
public:
  /**
   * @brief Counterexample type for this CEGIS component.
   *
   * @details Counterexamples give a set of assignments (variable names and
   * corresponding assignments) for which the previous solution violates the
   * safety property.
   */
  typedef std::map<const irep_idt, exprt> counterexamplet;

  /**
   * @brief
   *
   * @details
   *
   * @param st
   * @param gf
   * @param options
   * @param lfactory
   * @param synthesis_property
   */
  test_case_factoryt(symbol_tablet &st, goto_functionst &gf,
      const cegis_optionst &options, source_location_factoryt &lfactory,
      const exprt &synthesis_property);

  /**
   * @brief
   *
   * @details
   */
  ~test_case_factoryt();

  /**
   * @brief
   *
   * @details
   *
   * @param ce
   */
  void operator()(const counterexamplet &ce);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  size_t get_counterexample_count() const;
};

/**
 * @brief
 *
 * @details
 *
 * @param gf
 * @param options
 * @param lfactory
 * @param safety_property
 * @param counterexample_count
 */
void add_result_verification_assertion(goto_functionst &gf,
    const cegis_optionst &options, source_location_factoryt &lfactory,
    const exprt &safety_property, const size_t counterexample_count);

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param gf
 * @param options
 * @param lfactory
 * @param prop
 * @parap first
 * @param last
 * @tparam counterexample_iterator
 */
template<class counterexampe_iterator>
void add_symex_test_cases(class symbol_tablet &st, class goto_functionst &gf,
    const class cegis_optionst &options,
    class source_location_factoryt &lfactory, const exprt &prop,
    counterexampe_iterator first, counterexampe_iterator last)
{
  test_case_factoryt tf(st, gf, options, lfactory, prop);
  for (counterexampe_iterator it=first; it != last; ++it)
    tf(*it);
  const size_t count=tf.get_counterexample_count();
  add_result_verification_assertion(gf, options, lfactory, prop, count);
}

#endif /* CEGIS_SYMEX_TEST_CASE_FACTORY_H_ */
