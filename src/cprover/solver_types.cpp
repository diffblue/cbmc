/*******************************************************************\

Module: Solver Types

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Solver Types

#include "solver_types.h"

#include <util/format_expr.h>

#include "free_symbols.h"

#include <iostream>
#include <set>

void framet::add_auxiliary(exprt invariant)
{
  if(invariant.id() == ID_and)
  {
    for(const auto &conjunct : to_and_expr(invariant).operands())
      add_auxiliary(conjunct);
  }
  else
  {
    auxiliaries_set.insert(invariant);
    auxiliaries.push_back(std::move(invariant));
  }
}

void framet::add_invariant(exprt invariant)
{
  if(invariant.id() == ID_and)
  {
    for(const auto &conjunct : to_and_expr(invariant).operands())
      add_invariant(conjunct);
  }
  else
  {
    invariants_set.insert(invariant);
    invariants.push_back(std::move(invariant));
  }
}

void framet::add_obligation(exprt obligation)
{
  if(obligation.id() == ID_and)
  {
    for(const auto &conjunct : to_and_expr(obligation).operands())
      add_obligation(conjunct);
  }
  else
  {
    obligations_set.insert(obligation);
    obligations.push_back(std::move(obligation));
  }
}

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

      for(auto &i : f.obligations)
        std::cout << " obligation: " << format(i) << '\n';

      for(auto &i : f.auxiliaries)
        std::cout << "  auxiliary: " << format(i) << '\n';
    }

    if(property.frame == f.ref)
      std::cout << "  property: " << format(property.condition) << '\n';
  }
}
