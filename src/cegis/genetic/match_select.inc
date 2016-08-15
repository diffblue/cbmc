#include <cstdlib>
#include <iterator>

template<class populationt>
match_selectt<populationt>::match_selectt(const test_case_datat &test_case_data,
    const std::function<unsigned int()> random, const size_t rounds) :
    test_case_data(test_case_data), next_random_unsigned_int(random), rounds(
        rounds)
{
}

template<class populationt>
match_selectt<populationt>::match_selectt(const test_case_datat &test_case_data,
    const size_t rounds) :
    test_case_data(test_case_data), next_random_unsigned_int(::rand), rounds(
        rounds)
{
}

template<class populationt>
match_selectt<populationt>::~match_selectt()
{
}

namespace
{
template<class contestantt>
class is_contestant_less_thant
{
  const contestantt no_contestant;
public:
  is_contestant_less_thant(const contestantt &no_contestant) :
      no_contestant(no_contestant)
  {
  }

  bool operator()(const contestantt &lhs, const contestantt &rhs) const
  {
    const bool is_rhs_null=no_contestant == rhs;
    if (no_contestant == lhs) return !is_rhs_null;
    if (is_rhs_null) return false;
    return lhs->fitness < rhs->fitness;
  }
};

template<class populationt>
size_t get_match_fitness(
    const typename match_selectt<populationt>::test_case_datat &data,
    const typename match_selectt<populationt>::contestantt &no_contestant,
    const typename match_selectt<populationt>::contestantt &father,
    const typename match_selectt<populationt>::contestantt &mother)
{
  typedef typename match_selectt<populationt>::test_case_datat::const_iterator test_data_const_iterator;
  const test_data_const_iterator f=data.find(&*father);
  assert(data.end() != f);
  const test_data_const_iterator m=data.find(&*mother);
  assert(data.end() != m);
  const std::list<bool> &f_dt=f->second;
  const std::list<bool> &m_dt=m->second;
  const size_t f_data_size=f_dt.size();
  assert(f_data_size == m_dt.size());
  size_t match_value=mother->fitness;
  typedef std::list<bool>::const_iterator itert;
  for (itert fv=f_dt.begin(), mv=m_dt.begin(); fv != f_dt.end(); ++fv, ++mv)
    if (*fv != *mv) match_value+=2; // Excessive?
  return match_value;
}
}

template<class populationt>
typename match_selectt<populationt>::selectiont match_selectt<populationt>::select(
    populationt &pop) const
{
  const contestantt no_contestant=pop.end();
  const is_contestant_less_thant<contestantt> is_less_than(no_contestant);
  contestantt father=no_contestant;
  for (size_t contestants=0; contestants < rounds / 2;)
  {
    const contestantt contestant=std::next(pop.begin(), next_random_unsigned_int() % pop.size());
    if (father == contestant) continue;
    if (is_less_than(father, contestant)) father=contestant;
    ++contestants;
  }
  contestantt mother=no_contestant;
  size_t match_fitness=0u;
  for (size_t contestants=0; contestants < rounds / 2;)
  {
    const contestantt contestant=std::next(pop.begin(), next_random_unsigned_int() % pop.size());
    if (mother == contestant || father == contestant) continue;
    if (no_contestant == mother) mother=contestant;
    else
    {
      const size_t new_match=get_match_fitness<populationt>(test_case_data,
          no_contestant, father, contestant);
      if (match_fitness < new_match)
      {
        match_fitness=new_match;
        mother=contestant;
      }
    }
    ++contestants;
  }
  contestantt son=no_contestant;
  contestantt daughter=no_contestant;
  for (size_t contestants=0; contestants < rounds / 2;)
  {
    const contestantt contestant=std::next(pop.begin(), next_random_unsigned_int() % pop.size());
    if (father == contestant || mother == contestant || son == contestant
        || daughter == contestant) continue;
    if (no_contestant == son) son=contestant;
    else if (no_contestant == daughter) daughter=contestant;
    else if (son->fitness > contestant->fitness)
    {
      daughter=son;
      son=contestant;
    } else if (daughter->fitness > contestant->fitness) daughter=contestant;
    ++contestants;
  }
  selectiont selection;
  selection.parents.push_back(father);
  assert(no_contestant != father);
  selection.parents.push_back(mother);
  assert(no_contestant != mother);
  selection.children.push_back(son);
  assert(no_contestant != son);
  selection.children.push_back(daughter);
  assert(no_contestant != daughter);
  return selection;
}
