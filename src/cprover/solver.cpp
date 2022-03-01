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

#include <solvers/sat/satcheck.h>

#include "address_taken.h"
#include "axioms.h"
#include "bv_pointers_wide.h"
#include "console.h"
#include "counterexample_found.h"
#include "free_symbols.h"
#include "propagate.h"
#include "report_properties.h"
#include "report_traces.h"
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

void framet::add_invariant(exprt invariant)
{
  if(invariant.id() == ID_and)
  {
    for(const auto &conjunct : to_and_expr(invariant).operands())
      add_invariant(conjunct);
  }
  else
    invariants.push_back(std::move(invariant));
}

void framet::add_auxiliary(exprt invariant)
{
  if(invariant.id() == ID_and)
  {
    for(const auto &conjunct : to_and_expr(invariant).operands())
      add_auxiliary(conjunct);
  }
  else
    auxiliaries.push_back(std::move(invariant));
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

bool is_subsumed(
  const std::vector<exprt> &a1,
  const std::vector<exprt> &a2,
  const exprt &b,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  bool verbose,
  const namespacet &ns)
{
  if(b.is_true())
    return true; // anything subsumes 'true'

  for(auto &a_conjunct : a1)
    if(a_conjunct.is_false())
      return true; // 'false' subsumes anything

  for(auto &a_conjunct : a1)
    if(a_conjunct == b)
      return true; // b is subsumed by a conjunct in a

  cout_message_handlert message_handler;
  message_handler.set_verbosity(verbose ? 10 : 1);
  satcheckt satcheck(message_handler);
  bv_pointers_widet solver(ns, satcheck, message_handler);
  axiomst axioms(solver, address_taken, verbose, ns);

  // check if a => b is valid,
  // or (!a || b) is valid,
  // or (a && !b) is unsat
  for(auto &a_conjunct : a1)
    axioms << a_conjunct;

  for(auto &a_conjunct : a2)
    axioms << a_conjunct;

  axioms.set_to_false(b);

  // instantiate our axioms
  axioms.emit();

  // now run solver
  switch(solver())
  {
  case decision_proceduret::resultt::D_SATISFIABLE:
    if(verbose)
      show_assignment(solver);
    return false;
  case decision_proceduret::resultt::D_UNSATISFIABLE:
    return true;
  case decision_proceduret::resultt::D_ERROR:
    throw "error reported by solver";
  }

  UNREACHABLE; // to silence a warning
}

std::size_t count_frame(const workt::patht &path, frame_reft f)
{
  return std::count_if(path.begin(), path.end(), [f](const frame_reft &frame) {
    return f == frame;
  });
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
  const auto frame_map = build_frame_map(frames);
  auto &property = properties[property_index];

  property.start = std::chrono::steady_clock::now();
  take_time_resourcet stop_time(property.stop);

  if(solver_options.verbose)
    std::cout << "\nDoing " << format(property.condition) << '\n';

  for(auto &frame : frames)
    frame.reset();

  // add properties proven so far as auxiliaries
  for(std::size_t i = 0; i < property_index; i++)
  {
    const auto &p = properties[i];
    if(p.status == propertyt::PASS)
      frames[p.frame.index].add_auxiliary(p.condition);
  }

  std::vector<workt> queue;
  std::vector<workt> dropped;

  auto propagator =
    [&frames,
     &frame_map,
     &queue,
     &dropped,
     &address_taken,
     &solver_options,
     &ns](
      const symbol_exprt &symbol, exprt invariant, const workt::patht &path) {
      auto frame_ref = find_frame(frame_map, symbol);
      auto &f = frames[frame_ref.index];

      if(solver_options.verbose)
      {
        std::cout << "F: " << format(symbol) << " <- " << format(invariant)
                  << '\n';
      }

      // check if already subsumed
      if(is_subsumed(
           f.invariants,
           f.auxiliaries,
           invariant,
           address_taken,
           solver_options.verbose,
           ns))
      {
        if(solver_options.verbose)
          std::cout << "*** SUBSUMED\n";
      }
      else if(count_frame(path, frame_ref) > solver_options.loop_limit)
      {
        // loop limit exceeded, drop it
        if(solver_options.verbose)
          std::cout << "*** DROPPED\n";
        dropped.push_back(workt(frame_ref, invariant, path));
      }
      else
      {
        auto new_path = path;
        new_path.push_back(frame_ref);
        queue.emplace_back(f.ref, std::move(invariant), std::move(new_path));
      }
    };

  // we start with I = P
  queue.emplace_back(
    property.frame, property.condition, workt::patht{property.frame});

  while(!queue.empty())
  {
    auto work = queue.back();
    queue.pop_back();

    frames[work.frame.index].add_invariant(work.invariant);

    if(solver_options.verbose)
    {
      dump(frames, property, true, true);
      std::cout << '\n';
    }

    auto counterexample_found = ::counterexample_found(
      frames, work, address_taken, solver_options.verbose, ns);

    if(counterexample_found)
    {
      property.status = propertyt::REFUTED;
      property.trace = counterexample_found.value();
      return;
    }

    propagate(
      frames, work, address_taken, solver_options.verbose, ns, propagator);
  }

  // did we drop anything?
  if(dropped.empty())
    property.status = propertyt::PASS;
  else
    property.status = propertyt::DROPPED;
}

void solver_progress(size_t i, size_t n, bool verbose)
{
  if(verbose)
  {
  }
  else
  {
    if(i == n)
    {
      if(consolet::is_terminal())
        std::cout << "\x1b[1A\x1b[0K"; // clear the line
    }
    else
    {
      if(i != 0 && consolet::is_terminal())
        std::cout << "\x1b[1A";

      std::cout << consolet::orange << "Doing property " << (i + 1) << '/' << n
                << consolet::reset << '\n';
    }
  }
}

solver_resultt solver(
  const std::vector<exprt> &constraints,
  const solver_optionst &solver_options,
  const namespacet &ns)
{
  const auto address_taken = ::address_taken(constraints);

  if(solver_options.verbose)
  {
    for(auto &a : address_taken)
      std::cout << "address_taken: " << format(a) << '\n';
  }

  auto frames = setup_frames(constraints);

  find_implications(constraints, frames);

  auto properties = find_properties(constraints, frames);

  if(properties.empty())
  {
    std::cout << "\nThere are no properties to show.\n";
    return solver_resultt::ALL_PASS;
  }

  // solve each property separately, in order of occurence
  for(std::size_t i = 0; i < properties.size(); i++)
  {
    solver_progress(i, properties.size(), solver_options.verbose);
    solver(frames, address_taken, solver_options, ns, properties, i);
  }

  solver_progress(properties.size(), properties.size(), solver_options.verbose);

  // reporting
  report_properties(properties);

  if(solver_options.trace)
    report_traces(frames, properties, solver_options.verbose, ns);

  // overall outcome
  return overall_outcome(properties);
}
