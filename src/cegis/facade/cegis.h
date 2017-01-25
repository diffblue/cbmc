/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_FACADE_CEGIS_H
#define CPROVER_CEGIS_FACADE_CEGIS_H

#include <cstddef>

/**
 * @brief CEGIS template algorithm.
 *
 * @details Counterexample-guided inductive synthesis implementation
 * relying on generic learning algorithms and verification oracles.
 *
 * @param preproc The preprocessing configuration.
 * @param learn The learning algorithm to use.
 * @param oracle The verification oracle to use.
 * @param os Stream for solution output.
 *
 * @tparam learnt CEGIS learning algorithm type (e.g. GA).
 * @tparam oraclet CEGIS verification oracle type (e.g BMC).
 * @tparam preproct
 * @tparam mstreamt
 */
template<class learnt, class oraclet, class preproct, class seedt, class mstreamt>
int run_cegis(learnt &learn, oraclet &oracle, preproct &preproc, seedt &seed, size_t max_size, mstreamt &os)
{
  preproc();
  const size_t min_size=preproc.get_min_solution_size();
  preproc(min_size);
  learn.set_solution_size_range(min_size, max_size);
  learn.seed(seed);
  do
  {
    const typename learnt::candidatet &candidate=learn.next_candidate();
    oracle.verify(candidate);
  } while (oracle.has_counterexamples()
        && learn.learn(oracle.counterexamples_begin(), oracle.counterexamples_end()));
  if (oracle.success())
  {
    learn.show_candidate(os);
    return 0;
  }
  return 10;
}

#endif // CPROVER_CEGIS_FACADE_CEGIS_H
