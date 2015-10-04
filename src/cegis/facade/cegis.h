/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_H
#define CPROVER_CEGIS_H

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
template<class learnt, class oraclet, class preproct, class mstreamt>
int run_cegis(learnt &learn, oraclet &oracle, preproct &preproc, size_t max_size, mstreamt &os)
{
  preproc();
  const size_t min_size=preproc.get_min_solution_size();
  for (size_t max_solution_length=min_size; max_solution_length < max_size ; ++max_solution_length)
  {
    preproc(max_solution_length);
    learn.learn(max_solution_length);
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
  }
  return 10;
}

#endif /* CPROVER_CEGIS_H */
