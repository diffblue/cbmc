/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>
#include <cstdlib>

#include <cegis/genetic/random_individual.h>
#include <cegis/genetic/tournament_select.h>

#define MUTATION_OPS 2u

bool tournament_selectt::selectiont::can_mutate() const
{
  return parents.size() >= MUTATION_OPS;
}

#define NUM_PARENTS 2u
#define NUM_CHILDREN 2u

bool tournament_selectt::selectiont::can_cross() const
{
  return parents.size() >= NUM_PARENTS && children.size() >= NUM_CHILDREN;
}

tournament_selectt::individualt &tournament_selectt::selectiont::mutation_lhs()
{
  return *children.front();
}

const tournament_selectt::individualt &tournament_selectt::selectiont::mutation_rhs() const
{
  return *parents.front();
}

tournament_selectt::tournament_selectt(random_individualt &random,
    size_t pop_size, size_t rounds) :
    random(random), pop_size(pop_size), rounds(rounds)
{
}

tournament_selectt::~tournament_selectt()
{
}

void tournament_selectt::init(populationt &pop)
{
  pop.resize(pop_size);
  for (program_individualt &ind : pop)
    random.havoc(ind);
}

namespace
{
typedef tournament_selectt::populationt::iterator contestantt;

class arenat
{
  const contestantt no_contestant;
  contestantt father;
  contestantt mother;
  contestantt son;
  contestantt daughter;

  bool contains(const contestantt &c)
  {
    return father == c || mother == c || son == c || daughter == c;
  }
public:
  arenat(tournament_selectt::populationt &pop) :
      no_contestant(pop.end()), father(no_contestant), mother(no_contestant), son(
          no_contestant), daughter(no_contestant)
  {
  }

  bool add_contestant(const contestantt &contestant)
  {
    if (contains(contestant)) return false;
    if (no_contestant == father) father=contestant;
    else if (no_contestant == mother) mother=contestant;
    else if (no_contestant == son) son=contestant;
    else if (no_contestant == daughter) daughter=contestant;
    else if (father->fitness < contestant->fitness)
    {
      mother=father;
      father=contestant;
    } else if (mother->fitness < contestant->fitness) mother=contestant;
    else if (daughter->fitness > contestant->fitness)
    {
      son=daughter;
      daughter=contestant;
    } else if (son->fitness > contestant->fitness) son=contestant;
    return true;
  }

  void select(tournament_selectt::selectiont &selection)
  {
    selection.parents.push_back(father);
    selection.parents.push_back(mother);
    selection.children.push_back(son);
    selection.children.push_back(daughter);
  }
};
}

tournament_selectt::selectiont tournament_selectt::select(populationt &pop)
{
  arenat arena(pop);
  for (size_t contestants=0; contestants < rounds;)
  {
    populationt::iterator contestant=pop.begin();
    std::advance(contestant, rand() % pop.size());
    if (arena.add_contestant(contestant)) ++contestants;
  }
  tournament_selectt::selectiont selection;
  arena.select(selection);
  return selection;
}
