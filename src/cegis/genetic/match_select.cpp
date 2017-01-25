/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/genetic/random_individual.h>
#include <cegis/genetic/match_select.h>

match_selectt::match_selectt(const test_case_datat &test_case_data,
    random_individualt &random, size_t pop_size, size_t rounds) :
    test_case_data(test_case_data), random(random), pop_size(pop_size), rounds(
        rounds)
{
}

match_selectt::~match_selectt()
{
}

void match_selectt::init(populationt &pop)
{
  pop.resize(pop_size);
  for (program_individualt &ind : pop)
    random.havoc(ind);
}

bool match_selectt::selectiont::can_cross() const
{
  return true;
}

bool match_selectt::selectiont::can_mutate() const
{
  return true;
}

match_selectt::individualt &match_selectt::selectiont::mutation_lhs()
{
  return *children.front();
}

const match_selectt::individualt &match_selectt::selectiont::mutation_rhs() const
{
  return *parents.front();
}

namespace
{
typedef match_selectt::populationt::iterator contestantt;

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

size_t get_match_fitness(const match_selectt::test_case_datat &data,
    const contestantt &no_contestant, const contestantt &father,
    const contestantt &mother)
{
  const match_selectt::test_case_datat::const_iterator f=data.find(&*father);
  assert(data.end() != f);
  const match_selectt::test_case_datat::const_iterator m=data.find(&*mother);
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

match_selectt::selectiont match_selectt::select(populationt &pop)
{
  const contestantt no_contestant=pop.end();
  const is_contestant_less_thant is_less_than(no_contestant);
  contestantt father=no_contestant;
  for (size_t contestants=0; contestants < rounds / 2;)
  {
    contestantt contestant=pop.begin();
    std::advance(contestant, random.rand() % pop.size());
    if (father == contestant) continue;
    if (is_less_than(father, contestant)) father=contestant;
    ++contestants;
  }
  contestantt mother=no_contestant;
  size_t match_fitness=0u;
  for (size_t contestants=0; contestants < rounds / 2;)
  {
    contestantt contestant=pop.begin();
    std::advance(contestant, random.rand() % pop.size());
    if (mother == contestant || father == contestant) continue;
    if (no_contestant == mother) mother=contestant;
    else
    {
      const size_t new_match=get_match_fitness(test_case_data, no_contestant,
          father, contestant);
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
    contestantt contestant=pop.begin();
    std::advance(contestant, random.rand() % pop.size());
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
