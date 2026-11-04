/*******************************************************************\

Module: Counterexample Found

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Counterexample Found

#include "counterexample_found.h"

#include <util/cout_message.h>
#include <util/simplify_expr.h>

#include <solvers/decision_procedure.h>

#include "axioms.h"
#include "simplify_state_expr.h"
#include "state.h"
#include "state_encoding_solver_factory.h"

#include <memory>

void show_assignment(const decision_proceduret &)
{
  // no-op: debug output not available for generic decision procedures
}

static exprt evaluator_rec(
  const std::unordered_map<exprt, exprt, irep_hash> &memory,
  const decision_proceduret &solver,
  exprt src,
  const namespacet &ns)
{
  if(src.id() == ID_evaluate)
  {
    const auto &evaluate_expr = to_evaluate_expr(src);

    // recursively get the address
    auto address_evaluated =
      evaluator_rec(memory, solver, evaluate_expr.address(), ns);

    auto address_simplified =
      simplify_expr(simplify_state_expr(address_evaluated, {}, ns), ns);

    auto m_it = memory.find(address_simplified);
    if(m_it == memory.end())
      return src;
    else
      return m_it->second;
  }
  else if(src.id() == ID_symbol)
  {
    // nondet -- ask the solver
    return solver.get(src);
  }
  else
  {
    for(auto &op : src.operands())
      op = evaluator_rec(memory, solver, op, ns);

    return src;
  }
}

static exprt evaluator(
  const std::unordered_map<exprt, exprt, irep_hash> &memory,
  const decision_proceduret &solver,
  exprt src,
  const namespacet &ns)
{
  auto tmp = evaluator_rec(memory, solver, src, ns);
  return simplify_expr(simplify_state_expr(tmp, {}, ns), ns);
}

propertyt::tracet counterexample(
  const std::vector<framet> &frames,
  const workt &work,
  const decision_proceduret &solver,
  const axiomst &axioms,
  const namespacet &ns)
{
  propertyt::tracet trace;

  // map from memory addresses to memory values
  std::unordered_map<exprt, exprt, irep_hash> memory;

  // heap object counter
  std::size_t heap_object_counter = 0;

  // work.path goes backwards, we want a forwards trace
  for(auto r_it = work.path.rbegin(); r_it != work.path.rend(); ++r_it)
  {
    const auto &frame = frames[r_it->index];
    propertyt::trace_statet state;
    state.frame = *r_it;

    for(auto &implication : frame.implications)
    {
      if(implication.rhs.arguments().size() != 1)
        continue;
      auto &argument = implication.rhs.arguments().front();
      if(argument.id() == ID_update_state)
      {
        const auto &update_state = to_update_state_expr(argument);
        auto address = evaluator(memory, solver, update_state.address(), ns);
        auto value = evaluator(memory, solver, update_state.new_value(), ns);

        if(value.id() == ID_allocate)
        {
          // replace by a numbered 'heap object'
          heap_object_counter++;
          auto object_type = to_pointer_type(value.type()).base_type();
          auto identifier = "heap-" + std::to_string(heap_object_counter);
          value = object_address_exprt(symbol_exprt(identifier, object_type));
        }

        state.updates.emplace_back(address, value);
        memory[address] = value;
      }
      else if(argument.id() == ID_enter_scope_state)
      {
        // do we have a value?
        const auto &enter_scope_state = to_enter_scope_state_expr(argument);
        auto address = enter_scope_state.address();
        auto evaluate_expr = evaluate_exprt(enter_scope_state.state(), address);
        auto translated = axioms.translate(evaluate_expr);
        auto value = solver.get(translated);
        if(value.is_not_nil() && value != evaluate_expr)
        {
          state.updates.emplace_back(address, value);
          memory[address] = value;
        }
      }
    }

    trace.push_back(std::move(state));
  }

  return trace;
}

std::optional<propertyt::tracet> counterexample_found(
  const std::vector<framet> &frames,
  const workt &work,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  bool verbose,
  const namespacet &ns,
  const std::string &smt2_solver_binary)
{
  auto &f = frames[work.frame.index];

  for(const auto &implication : f.implications)
  {
    if(implication.lhs.id() == ID_initial_state)
    {
      cout_message_handlert message_handler;
      message_handler.set_verbosity(verbose ? 10 : 1);

      auto solver_bundle =
        make_state_encoding_solver(ns, smt2_solver_binary, message_handler);
      decision_proceduret &solver = solver_bundle.solver();

      axiomst axioms(solver, address_taken, verbose, ns);

      // These are initial states, i.e., initial_state(ς) ⇒ SInitial(ς).
      // Ask the solver whether the invariant is 'true'.
      axioms.set_to_false(work.invariant);
      axioms.set_to_true(implication.lhs);
      axioms.emit();

      switch(solver())
      {
      case decision_proceduret::resultt::D_SATISFIABLE:
        return counterexample(frames, work, solver, axioms, ns);
      case decision_proceduret::resultt::D_UNSATISFIABLE:
        break;
      case decision_proceduret::resultt::D_ERROR:
        // D_ERROR covers both hard solver errors and an "unknown" answer.
        // Treating it as "no counterexample" here would be unsound: the caller
        // could then declare the property inductive and report SUCCESS,
        // masking a genuine base-case violation.  Propagate the failure
        // instead, regardless of backend.
        throw "error reported by solver";
      }
    }
  }

  return {};
}
