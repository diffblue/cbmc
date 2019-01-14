/*******************************************************************\

Module: Memory model for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Memory model for partial order concurrency

#include "memory_model.h"

#include <util/std_expr.h>

memory_model_baset::memory_model_baset(const namespacet &_ns):
  partial_order_concurrencyt(_ns),
  var_cnt(0)
{
}

memory_model_baset::~memory_model_baset()
{
}

symbol_exprt memory_model_baset::nondet_bool_symbol(
  const std::string &prefix)
{
  return symbol_exprt(
    "memory_model::choice_"+prefix+std::to_string(var_cnt++),
    bool_typet());
}

bool memory_model_baset::po(event_it e1, event_it e2)
{
  // within same thread
  if(e1->source.thread_nr==e2->source.thread_nr)
    return numbering[e1]<numbering[e2];
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

  for(address_mapt::const_iterator
      a_it=address_map.begin();
      a_it!=address_map.end();
      a_it++)
  {
    const a_rect &a_rec=a_it->second;

    for(event_listt::const_iterator
        r_it=a_rec.reads.begin();
        r_it!=a_rec.reads.end();
        r_it++)
    {
      const event_it r=*r_it;

      exprt::operandst rf_some_operands;
      rf_some_operands.reserve(a_rec.writes.size());

      // this is quadratic in #events per address
      for(event_listt::const_iterator
          w_it=a_rec.writes.begin();
          w_it!=a_rec.writes.end();
          ++w_it)
      {
        const event_it w=*w_it;

        // rf cannot contradict program order
        if(po(r, w))
          continue; // contradicts po

        bool is_rfi=
          w->source.thread_nr==r->source.thread_nr;

        symbol_exprt s=nondet_bool_symbol("rf");

        // record the symbol
        choice_symbols[
          std::make_pair(r, w)]=s;

        // We rely on the fact that there is at least
        // one write event that has guard 'true'.
        implies_exprt read_from(s,
            and_exprt(w->guard,
              equal_exprt(r->ssa_lhs, w->ssa_lhs)));

        // Uses only the write's guard as precondition, read's guard
        // follows from rf_some
        add_constraint(equation,
          read_from, is_rfi?"rfi":"rf", r->source);

        if(!is_rfi)
        {
          // if r reads from w, then w must have happened before r
          const implies_exprt cond(s, before(w, r));
          add_constraint(equation,
            cond, "rf-order", r->source);
        }

        rf_some_operands.push_back(s);
      }

      // value equals the one of some write
      exprt rf_some;

      // uninitialised global symbol like symex_dynamic::dynamic_object*
      // or *$object
      if(rf_some_operands.empty())
        continue;
      else if(rf_some_operands.size()==1)
        rf_some=rf_some_operands.front();
      else
      {
        rf_some = or_exprt(std::move(rf_some_operands));
      }

      // Add the read's guard, each of the writes' guards is implied
      // by each entry in rf_some
      add_constraint(equation,
        implies_exprt(r->guard, rf_some), "rf-some", r->source);
    }
  }
}
