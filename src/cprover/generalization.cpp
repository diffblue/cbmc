/*******************************************************************\

Module: Generalization

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Generalization

#include "generalization.h"

#include <util/format_expr.h>

#include "console.h"
#include "solver.h"

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

void generalization(
  std::vector<framet> &frames,
  const workt &dropped,
  const propertyt &property,
  const solver_optionst &solver_options)
{
  // Look at the frame where we've given up
  auto &frame = frames[dropped.frame.index];

  if(solver_options.verbose)
  {
    for(auto &invariant : frame.invariants)
    {
      std::cout << consolet::green << "GI " << format(invariant)
                << consolet::reset << '\n';
    }
  }

  // We generalize by dropping disjuncts.
  // Look at the frequencies of the disjuncts in the proof obligation
  // among the candidate invariant and the previous obligations.
  frequency_mapt frequency_map(dropped.invariant);

  for(auto &i : frame.invariants)
    frequency_map(i);

  for(auto &o : frame.obligations)
    frequency_map(o);

  const auto frequencies = frequency_map.frequencies();

  if(solver_options.verbose)
  {
    for(auto entry : frequencies)
    {
      std::cout << "Freq " << entry->second << " " << format(entry->first)
                << "\n";
    }
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
  {
    auto new_invariant = disjunction(disjuncts);
    frame.add_invariant(new_invariant);
    if(solver_options.verbose)
      std::cout << consolet::yellow << "NI " << format(new_invariant)
                << consolet::reset << '\n';
  }
  else
  {
    // no, give up
  }
}
