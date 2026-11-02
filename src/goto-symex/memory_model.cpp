/*******************************************************************\

Module: Memory model for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Memory model for partial order concurrency

#include "memory_model.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/std_expr.h>

memory_model_baset::memory_model_baset(const namespacet &_ns)
  : partial_order_concurrencyt(_ns), var_cnt(0)
{
}

memory_model_baset::~memory_model_baset()
{
}

symbol_exprt memory_model_baset::nondet_bool_symbol(const std::string &prefix)
{
  return symbol_exprt(
    "memory_model::choice_" + prefix + std::to_string(var_cnt++), bool_typet());
}

bool memory_model_baset::po(event_it e1, event_it e2)
{
  // within same thread
  if(e1->source.thread_nr == e2->source.thread_nr)
    return numbering[e1] < numbering[e2];
  else
  {
    // in general un-ordered, with exception of thread-spawning
    return false;
  }
}

void memory_model_baset::read_from(symex_target_equationt &equation)
{
  // Encode the read-from relation (rf) as described in
  // Alglave/Kroening/Tautschnig CAV 2013, Section 4.2.
  //
  // For each read r at address a, we introduce Boolean choice variables
  // s_{w,r} for each candidate write w to address a. The constraints are:
  //
  //   rf-val:  s_{w,r} => alias(r,a) ∧ g(w) ∧ val(w) = val(r)
  //   rf-some: alias(r,a) ∧ g(r) => ∨_w s_{w,r}
  //   rf-order: s_{w,r} => before(w, r)  [for external rf]
  //
  // For may-alias reads (created for shared pointer dereferences in
  // concurrent context), the alias condition alias(r,a) guards both
  // rf-val and rf-some. This ensures that a may-alias read only needs
  // to read from writes at address a when the source pointer actually
  // points to a. Without this guard, a may-alias read distributed to
  // multiple addresses would be forced to read from ALL of them
  // simultaneously, making the constraints unsatisfiable.
  // See may_alias_soundness.md for the formal soundness argument.

  for(const auto &address : address_map)
  {
    for(const auto &read_event : address.second.reads)
    {
      exprt read_alias = alias_condition(read_event, address.first);

      exprt::operandst rf_choice_symbols;
      rf_choice_symbols.reserve(address.second.writes.size());

      // this is quadratic in #events per address
      for(const auto &write_event : address.second.writes)
      {
        // rf cannot contradict program order
        if(!po(read_event, write_event))
        {
          exprt write_alias = alias_condition(write_event, address.first);
          exprt alias_cond = conjunction({read_alias, write_alias});

          rf_choice_symbols.push_back(register_read_from_choice_symbol(
            read_event, write_event, equation, alias_cond));
        }
      }

      // uninitialised global symbol like symex_dynamic::dynamic_object*
      // or *$object
      if(!rf_choice_symbols.empty())
      {
        // Add the read's guard, each of the writes' guards is implied
        // by each entry in rf_some.
        // For may-alias reads, the rf-some constraint is conditional on
        // the pointer actually aliasing with this address. Without this
        // guard, a may-alias read added to multiple addresses would be
        // forced to read from ALL addresses simultaneously, which is
        // unsatisfiable and makes assertions vacuously true.
        // See Alglave/Kroening/Tautschnig CAV 2013 (Sec. 4.2, rf-some)
        // for the standard rf-some encoding.
        exprt guard = and_exprt{read_event->guard, read_alias};
        add_constraint(
          equation,
          implies_exprt{guard, disjunction(rf_choice_symbols)},
          "rf-some",
          read_event->source);
      }
    }
  }
}

symbol_exprt memory_model_baset::register_read_from_choice_symbol(
  const event_it &r,
  const event_it &w,
  symex_target_equationt &equation,
  const exprt &alias_cond)
{
  symbol_exprt s = nondet_bool_symbol("rf");

  // record the symbol
  choice_symbols.emplace(std::make_pair(r, w), s);

  bool is_rfi = w->source.thread_nr == r->source.thread_nr;
  // Uses only the write's guard as precondition, read's guard
  // follows from rf_some
  add_constraint(
    equation,
    // We rely on the fact that there is at least
    // one write event that has guard 'true'.
    // When the read and write have different types (due to may-alias
    // type compatibility), use byte_extract to reinterpret the write
    // value as the read's type. The expression simplifier will reduce
    // this to a typecast for same-width types or keep it as a proper
    // byte extraction for different widths.
    [&]()
    {
      exprt write_val = w->ssa_lhs;
      if(w->ssa_lhs.type() != r->ssa_lhs.type())
      {
        write_val = make_byte_extract(
          w->ssa_lhs, from_integer(0, c_index_type()), r->ssa_lhs.type());
      }
      return implies_exprt{
        s, and_exprt{alias_cond, w->guard, equal_exprt{r->ssa_lhs, write_val}}};
    }(),
    is_rfi ? "rfi" : "rf",
    r->source);

  if(!is_rfi)
  {
    // if r reads from w, then w must have happened before r
    add_constraint(
      equation, implies_exprt{s, before(w, r)}, "rf-order", r->source);
  }

  return s;
}
