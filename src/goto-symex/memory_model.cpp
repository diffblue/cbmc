/*******************************************************************\

Module: Memory model for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Memory model for partial order concurrency

#include "memory_model.h"

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
  // We iterate over all the reads, and
  // make them match at least one
  // (internal or external) write.

  for(const auto &address : address_map)
  {
    std::size_t r_w_property_counter = 0;
    for(const auto &read_event : address.second.reads)
    {
      exprt::operandst rf_choice_symbols;
      rf_choice_symbols.reserve(address.second.writes.size());

      // this is quadratic in #events per address
      for(const auto &write_event : address.second.writes)
      {
        // rf cannot contradict program order
        if(!po(read_event, write_event))
        {
          rf_choice_symbols.push_back(register_read_from_choice_symbol(
            read_event, write_event, equation, r_w_property_counter));
        }
      }

      // uninitialised global symbol like symex_dynamic::dynamic_object*
      // or *$object
      if(!rf_choice_symbols.empty())
      {
        // Add the read's guard, each of the writes' guards is implied
        // by each entry in rf_some
        add_constraint(
          equation,
          implies_exprt{read_event->guard, disjunction(rf_choice_symbols)},
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
  std::size_t &property_counter)
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
    implies_exprt{s, and_exprt{w->guard, equal_exprt{r->ssa_lhs, w->ssa_lhs}}},
    is_rfi ? "rfi" : "rf",
    r->source);

  if(!is_rfi)
  {
    // if r reads from w, then w must have happened before r
    add_constraint(
      equation, implies_exprt{s, before(w, r)}, "rf-order", r->source);
#if 0
    notequal_exprt ne{clock(w, axiomt::AX_PROPAGATION), clock(r, axiomt::AX_PROPAGATION)};
    const std::string sym_name = id2string(r->ssa_lhs.get_identifier());
    equation.assertion(
      simplify_expr(and_exprt{w->guard, r->guard}, ns),
      ne,
      sym_name + ".r_w_data_race." + std::to_string(++property_counter),
      "read/write data race on " + sym_name,
      r->source);
#endif
  }

  return s;
}
