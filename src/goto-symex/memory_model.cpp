/*******************************************************************\

Module: Memory model for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#include <util/std_expr.h>
#include <util/i2string.h>

#include "memory_model.h"

/*******************************************************************\

Function: memory_model_baset::memory_model_baset

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

memory_model_baset::memory_model_baset(const namespacet &_ns):
  partial_order_concurrencyt(_ns),
  var_cnt(0)
{
}

/*******************************************************************\

Function: memory_model_baset::~memory_model_baset

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

memory_model_baset::~memory_model_baset()
{
}

/*******************************************************************\

Function: memory_model_baset::nondet_bool_symbol

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt memory_model_baset::nondet_bool_symbol(
  const std::string &prefix)
{
  return symbol_exprt(
    "memory_model::choice_"+prefix+i2string(var_cnt++),
    bool_typet());
}

/*******************************************************************\

Function: memory_model_baset::po

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: memory_model_baset::write_symbol_primed

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

exprt memory_model_baset::write_symbol_primed(
  partial_order_concurrencyt::event_it e) const
{
  assert(is_shared_write(e));

  if(e->ssa_lhs.id()!=ID_symbol)
  {
    // initialisation
    assert(e->guard.is_true());
    return e->ssa_lhs;
  }

  const std::string name=
    id2string(to_symbol_expr(e->ssa_lhs).get_identifier()) + "$val";

  return symbol_exprt(name, e->ssa_lhs.type());
}

/*******************************************************************\

Function: memory_model_baset::read_from

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

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
      event_it r=*r_it;
      
      exprt::operandst rf_some_operands;
      rf_some_operands.reserve(a_rec.writes.size());

      // this is quadratic in #events per address
      for(event_listt::const_iterator
          w_it=a_rec.writes.begin();
          w_it!=a_rec.writes.end();
          ++w_it)
      {
        event_it w=*w_it;
        
        // rf cannot contradict program order
        if(po(*r_it, *w_it))
          continue; // contradicts po

        bool is_rfi=
          w->source.thread_nr==r->source.thread_nr;

        if(is_rfi)
        {
          // We only read from the most recent write of the same thread.
          // Extra wsi constraints ensure that even a
          // write with guard false will have the proper value.
          
          event_it e_it=*w_it;
          bool is_most_recent=true;
          for(++e_it; e_it!=*r_it && is_most_recent; ++e_it)
            is_most_recent&=!is_shared_write(e_it) ||
                            address(e_it)!=address(*r_it);

          if(!is_most_recent)
            continue;
        }

        symbol_exprt s=nondet_bool_symbol("rf");
        
        // record the symbol
        choice_symbols[
          std::make_pair(*r_it, *w_it)]=s;

        // We rely on the fact that there is at least
        // one write event that has guard 'true'.
        implies_exprt read_from(s,
            and_exprt((is_rfi ? true_exprt() : w->guard),
              equal_exprt(r->ssa_lhs, write_symbol_primed(w))));

        equation.constraint(
          true_exprt(), read_from, is_rfi?"rfi":"rf", r->source);

        if(!is_rfi)
        {
          // if r reads from w, then w must have happened before r
          exprt cond=implies_exprt(s, before(w, r));
          equation.constraint(
            true_exprt(), cond, "rf-order", r->source);
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
        rf_some=or_exprt();
        rf_some.operands().swap(rf_some_operands);
      }

      equation.constraint(
        r->guard, rf_some, "rf-some", r->source);
    }
  }
}

