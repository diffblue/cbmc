#include <cegis/cegis-util/irep_pipe.h>

template<class learner1t, class learner2t>
concurrent_learnt<learner1t, learner2t>::concurrent_learnt(learner1t &learner1,
    learner2t &learner2, const learner2_serialisert serialiser,
    const learner1_deserialisert deserialiser,
    const paragon_deserialisert encoded_deserialiser,
    const size_t learner1_head_start) :
    learner1(learner1), learner2(learner2), learner2_serialiser(serialiser), learner1_deserialiser(
        deserialiser), paragon_deserialiser(encoded_deserialiser), is_decoded_candidate(
        false), num_ces(0), num_symex_ces(learner1_head_start)
{
}

template<class learner1t, class learner2t>
template<class serialisert>
concurrent_learnt<learner1t, learner2t>::concurrent_learnt(learner1t &learner1,
    learner2t &learner2, serialisert serialiser,
    const size_t learner1_head_start) :
    learner1(learner1), learner2(learner2), learner2_serialiser(serialiser), learner1_deserialiser(
        serialiser), paragon_deserialiser(serialiser), is_decoded_candidate(
        false), num_ces(0), num_symex_ces(learner1_head_start)
{
}

template<class learner1t, class learner2t>
template<class seedt>
void concurrent_learnt<learner1t, learner2t>::seed(seedt &seed)
{
  learner1.seed(seed);
  learner2.seed(seed);
}

template<class learner1t, class learner2t>
const typename concurrent_learnt<learner1t, learner2t>::learner1_candidatet &concurrent_learnt<
    learner1t, learner2t>::next_candidate() const
{
  if (is_decoded_candidate) return decoded_candidate;
  return learner1.next_candidate();
}

template<class learner1t, class learner2t>
template<class itert>
bool concurrent_learnt<learner1t, learner2t>::learn(itert first,
    const itert &last)
{
  num_ces += std::distance(first, last);
  bool symex_running=true;
  learner1.set_termination_condition([this, &symex_running]()
  {
    task_pool.join_some();
    return symex_running;
  });
  bool symex_success=false;
  irep_pipet irep_pipe;
  const task_poolt::task_idt symex_task=task_pool.schedule(
      [this, first, last, &irep_pipe]() mutable
      {
        irep_pipe.close_read();
        try
        {
          const bool result=learner2.learn(first, last);
          if (!result) return EXIT_FAILURE;
          irept sdu;
          learner2_serialiser(sdu, learner2.next_candidate());
          irep_pipe.send(sdu);
          irep_pipe.close_write();
          return EXIT_SUCCESS;
        } catch(...)
        {
          irep_pipe.close_write();
          return EXIT_FAILURE;
        }
      }, [this, &symex_running, &symex_success, &irep_pipe](const int status)
      {
        if (EXIT_SUCCESS != status) return;
        symex_running=false;
        symex_success=true;
        irept sdu;
        irep_pipe.receive(sdu);
        learner2_candidatet ind;
        paragon_deserialiser(ind, sdu);
        learner1.add_paragon(ind);
        typename learner2t::candidatet symex_candidate;
        learner1_deserialiser(decoded_candidate, sdu);
        is_decoded_candidate=true;
      });
  irep_pipe.close_write();
  const bool genetic_success=learner1.learn(first, last);
  if (num_ces <= num_symex_ces)
    task_pool.join_all();
  if (symex_running) task_pool.cancel(symex_task);
  irep_pipe.close_read();
  if (genetic_success && !symex_success) is_decoded_candidate=false;
  learner2.add_counterexamples(first, last);
  return genetic_success || symex_success;
}

template<class learner1t, class learner2t>
void concurrent_learnt<learner1t, learner2t>::show_candidate(
    messaget::mstreamt &os) const
{
  if (is_decoded_candidate)
    learner1.show_candidate(os, decoded_candidate);
  else
    learner1.show_candidate(os);
}

template<class learner1t, class learner2t>
void concurrent_learnt<learner1t, learner2t>::set_solution_size_range(
    const size_t min, const size_t max)
{
  learner1.set_solution_size_range(min, max);
  learner2.set_solution_size_range(min, max);
}
