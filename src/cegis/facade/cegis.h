/*******************************************************************
 Module:  Counterexample-Guided Inductive Synthesis

 Authors: Daniel Kroening, kroening@kroening.com
 Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CPROVER_CEGIS_H
#define CPROVER_CEGIS_H

/**
 * @brief CEGIS common template algorithm.
 *
 * @details Counterexample-guided inductive synthesis implementation
 * relying on generic learning algorithms and verification oracles.
 *
 * @param learn The learning algorithm to use.
 * @param oracle The verification oracle to use.
 * @param os Stream for solution output.
 *
 * @tparam learnt CEGIS learning algorithm type (e.g. GA).
 * @tparam oraclet CEGIS verification oracle type (e.g BMC).
 */
template<class learnt, class oraclet, class mstreamt>
int run_cegis(learnt &learn, oraclet &oracle, mstreamt &os)
{
  do
  {
    const typename learnt::candidatet candidate(learn.next_candidate());
    oracle.verify(candidate);
  } while (oracle.has_counterexample()
      && learn.learn(oracle.get_counterexample()));
  if (oracle.success())
  {
    learn.show_candidate(os);
    return 0;
  }
  return 10;
}

#endif
