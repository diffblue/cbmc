/*******************************************************************\

Module: Solver

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Solver

#include "solver.h"

#include <util/cout_message.h>
#include <util/format_expr.h>
#include <util/std_expr.h>

#include "address_taken.h"
#include "console.h"
#include "free_symbols.h"
#include "inductiveness.h"
#include "report_properties.h"
#include "report_traces.h"
#include "solver_progress.h"
#include "solver_types.h"
#include "state.h"

#include <iomanip>
#include <iostream>
#include <map>
#include <set>

frame_mapt build_frame_map(const std::vector<framet> &frames)
{
  frame_mapt frame_map;

  for(std::size_t i = 0; i < frames.size(); i++)
    frame_map[frames[i].symbol] = frame_reft(i);

  return frame_map;
}

std::vector<framet> setup_frames(const std::vector<exprt> &constraints)
{
  std::set<symbol_exprt> states_set;
  std::vector<framet> frames;

  for(auto &c : constraints)
  {
    auto &location = c.source_location();
    free_symbols(c, [&states_set, &location, &frames](const symbol_exprt &s) {
      auto insert_result = states_set.insert(s);
      if(insert_result.second)
        frames.emplace_back(s, location, frame_reft(frames.size()));
    });
  }

  return frames;
}

void find_implications(
  const std::vector<exprt> &constraints,
  std::vector<framet> &frames)
{
  const auto frame_map = build_frame_map(frames);

  for(const auto &c : constraints)
  {
    // look for ∀ ς : state . Sxx(ς) ⇒ Syy(...)
    //      and ∀ ς : state . Sxx(ς) ⇒ ...
    if(c.id() == ID_forall && to_forall_expr(c).where().id() == ID_implies)
    {
      auto &implication = to_implies_expr(to_forall_expr(c).where());

      if(
        implication.rhs().id() == ID_function_application &&
        to_function_application_expr(implication.rhs()).function().id() ==
          ID_symbol)
      {
        auto &rhs_symbol = to_symbol_expr(
          to_function_application_expr(implication.rhs()).function());
        auto s_it = frame_map.find(rhs_symbol);
        if(s_it != frame_map.end())
        {
          frames[s_it->second.index].implications.emplace_back(
            implication.lhs(), to_function_application_expr(implication.rhs()));
        }
      }
    }
  }
}

frame_reft
find_frame(const frame_mapt &frame_map, const symbol_exprt &frame_symbol)
{
  auto entry = frame_map.find(frame_symbol);

  if(entry == frame_map.end())
    PRECONDITION(false);

  return entry->second;
}

std::vector<propertyt> find_properties(
  const std::vector<exprt> &constraints,
  const std::vector<framet> &frames)
{
  const auto frame_map = build_frame_map(frames);
  std::vector<propertyt> properties;

  for(const auto &c : constraints)
  {
    // look for ∀ ς : state . Sxx(ς) ⇒ ...
    if(c.id() == ID_forall && to_forall_expr(c).where().id() == ID_implies)
    {
      auto &implication = to_implies_expr(to_forall_expr(c).where());

      if(
        implication.rhs().id() != ID_function_application &&
        implication.lhs().id() == ID_function_application &&
        to_function_application_expr(implication.lhs()).function().id() ==
          ID_symbol)
      {
        auto &lhs_symbol = to_symbol_expr(
          to_function_application_expr(implication.lhs()).function());
        auto lhs_frame = find_frame(frame_map, lhs_symbol);
        properties.emplace_back(
          c.source_location(), lhs_frame, implication.rhs());
      }
    }
  }

  return properties;
}

exprt property_predicate(const implies_exprt &src)
{
  // Sxx(ς) ⇒ p(ς)
  return src.rhs();
}

void dump(
  const std::vector<framet> &frames,
  const propertyt &property,
  bool values,
  bool implications)
{
  for(const auto &f : frames)
  {
    std::cout << "FRAME: " << format(f.symbol) << '\n';

    if(implications)
    {
      for(auto &c : f.implications)
      {
        std::cout << "  implication: ";
        std::cout << format(c.lhs) << " -> " << format(c.rhs);
        std::cout << '\n';
      }
    }

    if(values)
    {
      for(auto &i : f.invariants)
        std::cout << "  invariant: " << format(i) << '\n';

      for(auto &i : f.auxiliaries)
        std::cout << "  auxiliary: " << format(i) << '\n';
    }

    if(property.frame == f.ref)
      std::cout << "  property: " << format(property.condition) << '\n';
  }
}

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

  if(solver_options.verbose)
    std::cout << "Doing " << format(property.condition) << '\n';

  // clean up
  for(auto &frame : frames)
    frame.reset();

  // we start with I = P
  frames[property.frame.index].add_invariant(property.condition);

  auto result =
    inductiveness_check(
      frames, address_taken, solver_options, ns, properties, property_index);

  switch(result)
  {
  case inductiveness_resultt::INDUCTIVE:
    property.status = propertyt::PASS;
    break;

  case inductiveness_resultt::BASE_CASE_FAIL:
    property.status = propertyt::REFUTED;
    break;

  case inductiveness_resultt::STEP_CASE_FAIL:
    property.status = propertyt::DROPPED;
    break;
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
