/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_GENETIC_SYMEX_FITNESS_H_
#define CEGIS_GENETIC_SYMEX_FITNESS_H_

/**
 * @brief
 *
 * @details
 *
 * @tparam populationt
 * @tparam test_runnert
 * @tparam counterexample_typet
 */
template<class populationt, class test_runnert, class counterexample_typet>
class lazy_fitnesst
{
public:
  typedef counterexample_typet counterexamplet;
  typedef std::deque<counterexamplet> counterexamplest;
  typedef typename populationt::value_type individualt;
  typedef typename populationt::iterator iterator;
  typedef std::map<const individualt *, std::list<bool> > test_case_datat;
private:
  test_runnert &test_runner;
  counterexamplest counterexamples;
  test_case_datat test_case_data;

  iterator find_candidate(populationt &pop);
public:
  /**
   * @brief
   *
   * @details
   *
   * @param test_runner
   */
  lazy_fitnesst(test_runnert &);

  /**
   * @brief
   *
   * @details
   */
  ~lazy_fitnesst();

  /**
   * @brief
   *
   * @details
   *
   * @param seed
   * @tparam seedt
   */
  template<class seedt>
  void seed(seedt &seed);

  /**
   * @brief
   *
   * @details
   *
   * @param ce
   */
  void add_test_case(const counterexamplet &ce);

  /**
   * @brief
   *
   * @details
   *
   * @param pop
   */
  iterator init(populationt &pop);

  /**
   * @brief
   *
   * @details
   *
   * @param individual
   */
  void set_fitness(individualt &individual);

  /**
   * @brief
   *
   * @details
   */
  typename individualt::fitnesst get_target_fitness() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const test_case_datat &get_test_case_data() const;
};

#include "lazy_fitness.inc"

#endif /* CEGIS_GENETIC_SYMEX_FITNESS_H_ */
