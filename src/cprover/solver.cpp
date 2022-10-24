/*******************************************************************\

Module: Solver

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Solver

#include "solver.h"

#include <util/console.h>
#include <util/cout_message.h>
#include <util/format_expr.h>
#include <util/std_expr.h>

#include "address_taken.h"
#include "counterexample_found.h"
#include "generalization.h"
#include "inductiveness.h"
#include "propagate.h"
#include "report_properties.h"
#include "report_traces.h"
#include "solver_progress.h"
#include "solver_types.h"
#include "state.h"

#include <iomanip>
#include <iostream>
#include <map>
#include <set>

class take_time_resourcet
{
public:
  explicit take_time_resourcet(
    std::chrono::time_point<std::chrono::steady_clock> &_dest)
    : dest(_dest)
  {
  }

  ~take_time_resourcet()
  {
    dest = std::chrono::steady_clock::now();
  }

protected:
  std::chrono::time_point<std::chrono::steady_clock> &dest;
};

void solver(
  std::vector<framet> &frames,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const solver_optionst &solver_options,
  const namespacet &ns,
  std::vector<propertyt> &properties,
  std::size_t property_index)
{
  auto &property = properties[property_index];

  property.start = std::chrono::steady_clock::now();
  take_time_resourcet stop_time(property.stop);

  // Clean up
  for(auto &frame : frames)
    frame.reset();

  // We start with I = P.
  frames[property.frame.index].add_invariant(property.condition);

  for(unsigned iteration = 0; true; iteration++)
  {
    if(iteration == 3) // limit the effort
    {
      property.status = propertyt::DROPPED;
      return; // give up
    }

    if(solver_options.verbose)
      std::cout << "Doing " << format(property.condition) << " iteration "
                << iteration + 1 << '\n';

    auto result = inductiveness_check(
      frames, address_taken, solver_options, ns, properties, property_index);

    switch(result.outcome)
    {
    case inductiveness_resultt::INDUCTIVE:
      property.status = propertyt::PASS;
      return; // done

    case inductiveness_resultt::BASE_CASE_FAIL:
      if(iteration == 0)
      {
        // no generalization done, so this is a counterexample
        property.status = propertyt::REFUTED;
        return; // DONE
      }
      else
      {
        // Invariant was generalized too much. Try something weaker.
        property.status = propertyt::DROPPED;
        return;
      }

    case inductiveness_resultt::STEP_CASE_FAIL:
      // Invariant is too weak or too strong to be inductive.
      generalization(frames, *result.work, property, solver_options);
      break;
    }
  }
}

solver_resultt solver(
  const std::vector<exprt> &constraints,
  const solver_optionst &solver_options,
  const namespacet &ns)
{
  const auto address_taken = ::address_taken(constraints);

#if 0
  if(solver_options.verbose)
  {
    for(auto &a : address_taken)
      std::cout << "address_taken: " << format(a) << '\n';
  }
#endif

  auto frames = setup_frames(constraints);

  find_implications(constraints, frames);

  auto properties = find_properties(constraints, frames);

  if(properties.empty())
  {
    std::cout << "\nThere are no properties to show.\n";
    return solver_resultt::ALL_PASS;
  }

  solver_progresst solver_progress(properties.size(), solver_options.verbose);

  // solve each property separately, in order of occurence
  for(std::size_t i = 0; i < properties.size(); i++)
  {
    solver_progress(i);
    solver(frames, address_taken, solver_options, ns, properties, i);
  }

  solver_progress.finished();

  // reporting
  report_properties(properties);

  if(solver_options.trace)
    report_traces(frames, properties, solver_options.verbose, ns);

  // overall outcome
  return overall_outcome(properties);
}
