/*******************************************************************\

Module: Solver

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Solver

#include "solver.h"

#include <util/arith_tools.h>
#include <util/cout_message.h>
#include <util/format_expr.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include <solvers/sat/satcheck.h>

#include "address_taken.h"
#include "axioms.h"
#include "bv_pointers_wide.h"
#include "console.h"
#include "counterexample_found.h"
#include "free_symbols.h"
#include "in_interval_expr.h"
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

static bool is_plus_one(const exprt &a, const exprt &b)
{
  if(a.id() == ID_constant && b.id() == ID_constant)
  {
    auto v_a = numeric_cast<mp_integer>(to_constant_expr(a));
    auto v_b = numeric_cast<mp_integer>(to_constant_expr(b));
    if(v_a.has_value() && v_b.has_value() && v_a.value() + 1 == v_b.value())
      return true;
  }

  return false;
}

static optionalt<in_interval_exprt>
make_in_interval(const exprt &a, const exprt &b)
{
  if(a.id() == ID_equal && b.id() == ID_equal)
  {
    if(to_equal_expr(a).lhs() == to_equal_expr(b).lhs())
    {
      // we look for x=a && x=a+1 on integers
      if(is_plus_one(to_equal_expr(a).rhs(), to_equal_expr(b).rhs()))
        return in_interval_exprt(
          to_equal_expr(a).lhs(),
          to_equal_expr(a).rhs(),
          to_equal_expr(b).rhs());
      else if(is_plus_one(to_equal_expr(b).rhs(), to_equal_expr(a).rhs()))
        return make_in_interval(b, a);
      else
        return {};
    }
    else
      return {};
  }
  else if(a.id() == ID_equal && b.id() == "in_interval")
  {
    return {};
  }
  else if(a.id() == "in_interval" && b.id() == ID_equal)
  {
    return make_in_interval(b, a);
  }
  else
    return {};
}

exprt simplify_invariant(exprt expr, const namespacet &ns)
{
  expr = simplify_expr(expr, ns);

  if(expr.id() == ID_or)
  {
    auto &ops = to_or_expr(expr).operands();
    bool replacement_done = false;
    for(std::size_t i = 1; i < ops.size(); i++)
    {
      auto in_interval = make_in_interval(ops[i - 1], ops[i]);
      if(in_interval.has_value())
      {
        ops[i - 1] = false_exprt();
        ops[i] = in_interval.value();
        replacement_done = true;
      }
    }

    if(replacement_done)
      expr = simplify_expr(expr, ns);
  }

  return expr;
}

bool is_subsumed(
  const std::unordered_set<exprt, irep_hash> &a1,
  const std::unordered_set<exprt, irep_hash> &a2,
  const exprt &b,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  bool verbose,
  const namespacet &ns)
{
  if(b.is_true())
    return true; // anything subsumes 'true'

  if(a1.find(false_exprt()) != a1.end())
    return true; // 'false' subsumes anything

  if(a1.find(b) != a1.end())
    return true; // b is subsumed by a conjunct in a

  cout_message_handlert message_handler;
#if 0
  message_handler.set_verbosity(verbose ? 10 : 1);
#else
  message_handler.set_verbosity(1);
#endif
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
    std::cout << "Doing " << format(property.condition) << '\n';

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

#if 0
      if(solver_options.verbose)
      {
        // print the current invariants in the frame
        for(const auto &invariant : f.invariants)
        {
          std::cout << consolet::faint << consolet::blue;
          std::cout << 'I' << std::setw(2) << frame_ref.index << ' ';
          std::cout << format(invariant);
          std::cout << consolet::reset << '\n';
        }

        std::cout << "\u2192" << consolet::faint << std::setw(2)
                  << frame_ref.index << consolet::reset << ' ';
      }
#endif

      invariant = simplify_invariant(invariant, ns);

      // trivially true?
      if(invariant.is_true())
      {
        if(solver_options.verbose)
          std::cout << "trivial\n";
      }
      else if(is_subsumed(
                f.invariants_set,
                f.auxiliaries_set,
                invariant,
                address_taken,
                solver_options.verbose,
                ns))
      {
        if(solver_options.verbose)
          std::cout << "subsumed " << format(invariant) << '\n';
      }
      else if(count_frame(path, frame_ref) > solver_options.loop_limit)
      {
        // loop limit exceeded, drop it
        if(solver_options.verbose)
          std::cout << consolet::red << "dropped" << consolet::reset << ' '
                    << format(invariant) << '\n';
        dropped.emplace_back(frame_ref, invariant, path);
      }
      else
      {
        // propagate
        if(solver_options.verbose)
          std::cout << format(invariant) << '\n';

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

#if 0
    if(solver_options.verbose)
    {
      dump(frames, property, true, true);
      std::cout << '\n';
    }
#endif

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
