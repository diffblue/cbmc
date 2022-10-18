/*******************************************************************\

Module: Generalization

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Generalization

#include "generalization.h"

#include <util/format_expr.h>

#include <iostream>
#include <map>

class frequency_mapt
{
public:
  explicit frequency_mapt(const exprt &expr)
  {
    setup_rec(expr);
  }

  void operator()(const exprt &expr)
  {
    count_rec(expr);
  }

  using counterst = std::map<exprt, std::size_t>;

  // return frequencies, highest to lowest
  std::vector<counterst::const_iterator> frequencies() const
  {
    std::vector<counterst::const_iterator> result;
    for(auto it = counters.begin(); it != counters.end(); it++)
      result.push_back(it);
    std::sort(
      result.begin(),
      result.end(),
      [](counterst::const_iterator a, counterst::const_iterator b) -> bool {
        return a->second >= b->second;
      });
    return result;
  }

protected:
  counterst counters;

  void count_rec(const exprt &expr)
  {
    if(expr.id() == ID_or)
    {
      for(auto &op : expr.operands())
        count_rec(op);
    }
    else
    {
      auto it = counters.find(expr);
      if(it != counters.end())
        it->second++;
    }
  }

  void setup_rec(const exprt &expr)
  {
    if(expr.id() == ID_or)
    {
      for(auto &op : expr.operands())
        setup_rec(op);
    }
    else
      counters.emplace(expr, 0);
  }
};

optionalt<exprt>
generalize(const framet &frame, exprt invariant, const namespacet &ns)
{
  // We generalize by dropping disjuncts.
  // Look at the frequencies of the disjuncts in the new VC.
  frequency_mapt frequency_map(invariant);

  for(auto &i : frame.invariants)
    frequency_map(i);

  const auto frequencies = frequency_map.frequencies();

  for(auto entry : frequencies)
  {
    std::cout << "E " << entry->second << " " << format(entry->first) << "\n";
  }

  // form disjunction of top ones
  exprt::operandst disjuncts;
  for(auto entry : frequencies)
  {
    if(entry->second == frequencies.front()->second)
      disjuncts.push_back(entry->first);
  }

  // Does this actually strengthen the formula?
  if(disjuncts.size() < frequencies.size())
    return disjunction(disjuncts);
  else
    return {}; // no, give up
}
