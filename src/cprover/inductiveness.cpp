/*******************************************************************\

Module: Inductiveness

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Inductiveness

#include "inductiveness.h"

#include <util/console.h>
#include <util/cout_message.h>
#include <util/format_expr.h>

#include <solvers/sat/satcheck.h>

#include "axioms.h"
#include "bv_pointers_wide.h"
#include "counterexample_found.h"
#include "propagate.h"
#include "solver.h"

#include <algorithm>
#include <iomanip>
#include <iostream>

bool is_subsumed(
  const std::unordered_set<exprt, irep_hash> &a1,
  const std::unordered_set<exprt, irep_hash> &a2,
  const std::unordered_set<exprt, irep_hash> &a3,
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

  for(auto &a_conjunct : a3)
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

inductiveness_resultt inductiveness_check(
  std::vector<framet> &frames,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const solver_optionst &solver_options,
  const namespacet &ns,
  std::vector<propertyt> &properties,
  std::size_t property_index)
{
  const auto frame_map = build_frame_map(frames);
  auto &property = properties[property_index];

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
        std::cout << "F: " << format(symbol) << " <- " << format(invariant)
                  << '\n';
      }
#endif

      if(solver_options.verbose)
      {
        // print the current invariants and obligations in the frame
        for(const auto &invariant : f.invariants)
        {
          std::cout << consolet::faint << consolet::blue;
          std::cout << 'I' << std::setw(2) << frame_ref.index << ' ';
          std::cout << format(invariant);
          std::cout << consolet::reset << '\n';
        }
        for(const auto &obligation : f.obligations)
        {
          std::cout << consolet::faint << consolet::blue;
          std::cout << 'O' << std::setw(2) << frame_ref.index << ' ';
          std::cout << format(obligation);
          std::cout << consolet::reset << '\n';
        }
      }

      if(solver_options.verbose)
        std::cout << "\u2192" << consolet::faint << std::setw(2)
                  << frame_ref.index << consolet::reset << ' ';

      // trivially true?
      if(invariant.is_true())
      {
        if(solver_options.verbose)
          std::cout << "trivial\n";
      }
      else if(is_subsumed(
                f.invariants_set,
                f.obligations_set,
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

        // store in frame
        frames[frame_ref.index].add_obligation(invariant);

        // add to queue
        auto new_path = path;
        new_path.push_back(frame_ref);
        queue.emplace_back(f.ref, std::move(invariant), std::move(new_path));
      }
    };

  // stick invariants into the queue
  for(std::size_t frame_index = 0; frame_index < frames.size(); frame_index++)
  {
    frame_reft frame_ref(frame_index);
    for(auto &cond : frames[frame_index].invariants)
      queue.emplace_back(frame_ref, cond, workt::patht{frame_ref});
  }

  // clean up the obligations
  for(auto &frame : frames)
  {
    frame.obligations.clear();
    frame.obligations_set.clear();
  }

  while(!queue.empty())
  {
    auto work = queue.back();
    queue.pop_back();

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
      property.trace = counterexample_found.value();
      return inductiveness_resultt::base_case_fail(std::move(work));
    }

    propagate(
      frames, work, address_taken, solver_options.verbose, ns, propagator);

    // did we drop anything?
    if(!dropped.empty())
      return inductiveness_resultt::step_case_fail(std::move(dropped.front()));
  }

  // done, saturated
  return inductiveness_resultt::inductive();
}
