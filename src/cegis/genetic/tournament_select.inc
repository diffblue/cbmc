#include <iterator>
#include <cstdlib>

template<class population_typet>
tournament_selectt<population_typet>::tournament_selectt(const size_t rounds) :
    rounds(rounds)
{
}

template<class population_typet>
tournament_selectt<population_typet>::~tournament_selectt()
{
}

namespace
{
template<class populationt>
class arenat
{
  typedef typename tournament_selectt<populationt>::contestantt contestantt;
  typedef typename tournament_selectt<populationt>::selectiont selectiont;
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
  arenat(populationt &pop) :
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

  void select(selectiont &selection)
  {
    selection.parents.push_back(father);
    selection.parents.push_back(mother);
    selection.children.push_back(son);
    selection.children.push_back(daughter);
  }
};
}

template<class population_typet>
typename tournament_selectt<population_typet>::selectiont tournament_selectt<
    population_typet>::select(populationt &pop)
{
  arenat<populationt> arena(pop);
  for (size_t contestants=0; contestants < rounds;)
  {
    const contestantt contestant=std::next(pop.begin(), rand() % pop.size());
    if (arena.add_contestant(contestant)) ++contestants;
  }
  tournament_selectt::selectiont selection;
  arena.select(selection);
  return selection;
}
