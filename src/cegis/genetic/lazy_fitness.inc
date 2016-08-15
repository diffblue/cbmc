#include <algorithm>

template<class populationt, class test_runnert, class counterexample_typet>
lazy_fitnesst<populationt, test_runnert, counterexample_typet>::lazy_fitnesst(
    test_runnert &test_runner) :
    test_runner(test_runner)
{
}

template<class populationt, class test_runnert, class counterexample_typet>
lazy_fitnesst<populationt, test_runnert, counterexample_typet>::~lazy_fitnesst()
{
}

template<class populationt, class test_runnert, class counterexample_typet>
template<class seedt>
void lazy_fitnesst<populationt, test_runnert, counterexample_typet>::seed(
    seedt &seeder)
{
  seeder(counterexamples);
}

template<class populationt, class test_runnert, class counterexample_typet>
void lazy_fitnesst<populationt, test_runnert, counterexample_typet>::add_test_case(
    const counterexamplet &ce)
{
  const typename counterexamplest::iterator end=counterexamples.end();
  assert(end == std::find(counterexamples.begin(), end, ce));
  counterexamples.push_back(ce);
}

template<class populationt, class test_runnert, class counterexample_typet>
typename lazy_fitnesst<populationt, test_runnert, counterexample_typet>::iterator lazy_fitnesst<
    populationt, test_runnert, counterexample_typet>::find_candidate(
    populationt &pop)
{
  const size_t ces=get_target_fitness();
  for (iterator it=pop.begin(); it != pop.end(); ++it)
    if (it->fitness == ces) return it;
  return pop.end();
}

namespace
{
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

template<class populationt, class test_runnert, class counterexample_typet>
typename lazy_fitnesst<populationt, test_runnert, counterexample_typet>::iterator lazy_fitnesst<
    populationt, test_runnert, counterexample_typet>::init(populationt &pop)
{
  const counterexamplest &ces=counterexamples;
  const size_t ce_count=ces.size();
  for (individualt &individual : pop)
  {
    std::list<bool> &ind_test_data=test_case_data[&individual];
    for (size_t i=ind_test_data.size(); i < ce_count; ++i)
      test_runner.run_test(individual, ces[i],
          test_callbackt<individualt>(individual, ind_test_data));
    const iterator candidate=find_candidate(pop);
    if (pop.end() != candidate)
    {
      test_runner.join();
      return candidate;
    }
  }
  test_runner.join();
  return find_candidate(pop);
}

template<class populationt, class test_runnert, class counterexample_typet>
void lazy_fitnesst<populationt, test_runnert, counterexample_typet>::set_fitness(
    individualt &individual)
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

template<class populationt, class test_runnert, class counterexample_typet>
typename lazy_fitnesst<populationt, test_runnert, counterexample_typet>::individualt::fitnesst lazy_fitnesst<
    populationt, test_runnert, counterexample_typet>::get_target_fitness() const
{
  size_t fitness=0;
  const size_t end=counterexamples.size();
  for (size_t i=0u; i < end; ++i)
    ++fitness;
  return fitness;
}

template<class populationt, class test_runnert, class counterexample_typet>
const typename lazy_fitnesst<populationt, test_runnert, counterexample_typet>::test_case_datat &lazy_fitnesst<
    populationt, test_runnert, counterexample_typet>::get_test_case_data() const
{
  return test_case_data;
}
