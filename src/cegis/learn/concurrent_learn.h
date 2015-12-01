/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_CONCURRENT_LEARN_H_
#define CEGIS_CONCURRENT_LEARN_H_

#include <functional>

#include <util/irep.h>
#include <util/task_pool.h>

/**
 * @brief
 *
 * @details
 */
template<class learner1t, class learner2t>
class concurrent_learnt
{
public:
  typedef typename learner1t::candidatet candidatet;
  typedef typename learner2t::candidatet encoded_candidatet;
  typedef typename learner1t::counterexamplet counterexamplet;
  typedef typename learner1t::counterexamplest counterexamplest;
  typedef std::function<void(irept &, const encoded_candidatet &)> serialisert;
  typedef std::function<void(candidatet &, const irept &)> deserialisert;
  typedef std::function<void(encoded_candidatet &, const irept &)> encoded_deserialisert;
private:
  learner1t &learner1;
  learner2t &learner2;
  task_poolt task_pool;
  const serialisert serialiser;
  const deserialisert deserialiser;
  const encoded_deserialisert encoded_deserialiser;
  bool is_decoded_candidate;
  candidatet decoded_candidate;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param learner1
   * @param learner2
   * @param serialiser
   * @param deserialiser
   * @param encoded_deserialiser
   */
  concurrent_learnt(learner1t &learner1, learner2t &learner2,
      serialisert serialiser, deserialisert deserialiser,
      encoded_deserialisert encoded_deserialiser);

  /**
   * @brief
   *
   * @details
   */
  ~concurrent_learnt();

  template<class seedt>
  void seed(seedt &seed);

  const candidatet &next_candidate() const;

  template<class itert>
  bool learn(itert first, const itert &last);

  void show_candidate(messaget::mstreamt &os) const;

  void set_solution_size_range(size_t min, size_t max);
};

#include "concurrent_learn.inc"

#endif /* CEGIS_CONCURRENT_LEARN_H_ */
