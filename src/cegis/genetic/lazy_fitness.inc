#include <algorithm>

#include <cbmc/cbmc_solvers.h>
#include <cbmc/bmc.h>

template<class test_runnert, class cet>
lazy_fitnesst<test_runnert, cet>::lazy_fitnesst(test_runnert &test_runner) :
    test_runner(test_runner)
{
}

template<class test_runnert, class cet>
lazy_fitnesst<test_runnert, cet>::~lazy_fitnesst()
{
}

template<class test_runnert, class cet>
template<class seedt>
void lazy_fitnesst<test_runnert, cet>::seed(seedt &seeder)
{
  seeder(counterexamples);
}

template<class test_runnert, class cet>
void lazy_fitnesst<test_runnert, cet>::add_test_case(const counterexamplet &ce)
{
  const typename counterexamplest::iterator end=counterexamples.end();
  assert(end == std::find(counterexamples.begin(), end, ce));
  counterexamples.push_back(ce);
}

template<class test_runnert, class cet>
typename lazy_fitnesst<test_runnert, cet>::populationt::iterator lazy_fitnesst<
    test_runnert, cet>::find_candidate(populationt &pop)
{
  const size_t ces=get_target_fitness();
  for (populationt::iterator it=pop.begin(); it != pop.end(); ++it)
    if (it->fitness == ces) return it;
  return pop.end();
}

namespace
{
size_t get_bounty(const size_t index)
{
  /*size_t bounty=1u;
   bounty+=index / 5u;
   return bounty;*/
  return 1u;
}

bool &new_test_result(std::list<bool> &test_case_data)
{
  test_case_data.push_back(false);
  return test_case_data.back();
}

template<class individualt>
class test_callbackt
{
  typename individualt::fitnesst &fitness;
  bool &test_result;
public:
  test_callbackt(individualt &ind, std::list<bool> &test_case_data) :
      fitness(ind.fitness), test_result(new_test_result(test_case_data))
  {
  }

  void operator()(const bool success)
  {
    if (success) ++fitness;
    test_result=success;
  }
};
}

template<class test_runnert, class cet>
typename lazy_fitnesst<test_runnert, cet>::populationt::iterator lazy_fitnesst<
    test_runnert, cet>::init(populationt &pop)
{
  const counterexamplest &ces=counterexamples;
  const size_t ce_count=ces.size();
  for (individualt &individual : pop)
  {
    std::list<bool> &ind_test_data=test_case_data[&individual];
    for (size_t i=ind_test_data.size(); i < ce_count; ++i)
      test_runner.run_test(individual, ces[i],
          test_callbackt<individualt>(individual, ind_test_data));
    const populationt::iterator candidate=find_candidate(pop);
    if (pop.end() != candidate)
    {
      test_runner.join();
      return candidate;
    }
  }
  test_runner.join();
  return find_candidate(pop);
}

template<class test_runnert, class cet>
void lazy_fitnesst<test_runnert, cet>::set_fitness(individualt &individual)
{
  individual.fitness=0u;
  std::list<bool> &ind_test_data=test_case_data[&individual];
  ind_test_data.clear();
  const size_t num_ces=counterexamples.size();
  for (size_t i=0; i < num_ces; ++i)
    test_runner.run_test(individual, counterexamples[i],
        test_callbackt<individualt>(individual, ind_test_data));
  test_runner.join();
}

template<class test_runnert, class cet>
typename lazy_fitnesst<test_runnert, cet>::individualt::fitnesst lazy_fitnesst<
    test_runnert, cet>::get_target_fitness() const
{
  size_t fitness=0;
  const size_t end=counterexamples.size();
  for (size_t i=0u; i < end; ++i)
    fitness+=get_bounty(i);
  return fitness;
}

template<class test_runnert, class cet>
const test_case_datat &lazy_fitnesst<test_runnert, cet>::get_test_case_data() const
{
  return test_case_data;
}
