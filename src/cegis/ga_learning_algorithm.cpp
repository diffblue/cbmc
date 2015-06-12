#include <cegis/ga_learning_algorithm.h>

ga_learning_algorithmt::candidatet ga_learning_algorithmt::next_candidate() const
{
  return candidatet();
}

bool ga_learning_algorithmt::learn(const counterexamplet &counterexample)
{
  return false;
}

void ga_learning_algorithmt::show_candidate(std::ostream &os) const
{
}
