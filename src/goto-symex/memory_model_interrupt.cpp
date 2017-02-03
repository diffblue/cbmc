/*******************************************************************\

Module: Memory model for partial order concurrency

Author: Lihao Liang, lihao.liang@cs.ox.ac.uk

\*******************************************************************/

#include <util/std_expr.h>
#include <algorithm>

#include "memory_model_interrupt.h"

/*******************************************************************\

Function: memory_model_interruptt::operator()

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_interruptt::operator()(symex_target_equationt &equation)
{
  print(8, "Adding interrupt constraints");

  build_event_lists(equation);
  build_clock_type(equation);
  build_per_thread_map(equation, per_thread_map);
 
  program_order(equation);
  read_from(equation);
  write_serialization_external(equation);
  from_read(equation);
}

/*******************************************************************\

Function: memory_model_interruptt::read_from

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_interruptt::read_from(symex_target_equationt &equation)
{
  memory_model_sct::read_from(equation);

  for(const auto &c_it : choice_symbols)
  {
    const event_it r=c_it.first.first;
    const event_it w=c_it.first.second;

    assert(!po(r, w));

    if(w->source.thread_nr!=r->source.thread_nr &&
       w->source.priority>=r->source.priority)
    { 
      // must use before(w, r) instead of c_it.second 
      exprt cond=implies_exprt(
        and_exprt(before(w, r), w->guard, r->guard), 
        last(w, r));
      add_constraint(
        equation, cond, "rf-irq", r->source);
    }
  }
}

/*******************************************************************\

Function: memory_model_interruptt::write_serialization_external

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_interruptt::write_serialization_external(
  symex_target_equationt &equation)
{
  memory_model_sct::write_serialization_external(equation);

  for(const auto &c_it : ww_pair_symbols)
  {
    const symbol_exprt &s=c_it.second;
    const event_it w1=c_it.first.first;
    const event_it w2=c_it.first.second;

    if(w1->source.priority>=
       w2->source.priority)
    {
      add_constraint(
        equation,
        implies_exprt(
          and_exprt(s, w1->guard, w2->guard), 
          last(w1, w2)),
        "ws-irq",
        w1->source);
    }

    if(w1->source.priority<=
       w2->source.priority)
    {
      add_constraint(
        equation,
        implies_exprt(
          and_exprt(not_exprt(s), w1->guard, w2->guard), 
          last(w2, w1)),
        "ws-irq",
        w1->source);
    }
  }
}

/*******************************************************************\

Function: memory_model_interruptt::from_read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_interruptt::from_read(symex_target_equationt &equation)
{
  // from-read: (w', w) in ws and (w', r) in rf -> (r, w) in fr
  memory_model_sct::from_read(equation);

  for(const auto &ww_pair_it : ww_pairs)
  {
    const event_it w_prime=ww_pair_it.first.first; 
    const event_it w=ww_pair_it.first.second;
    const exprt &ws1=ww_pair_it.second.first;
    const exprt &ws2=ww_pair_it.second.second;
     
    // smells like cubic
    for(const auto &c_it : choice_symbols)
    {
      const event_it r=c_it.first.first;
      const exprt &rf=c_it.second;
      exprt cond;
      cond.make_nil();
    
      if(c_it.first.second==w_prime && !ws1.is_false() &&
         r->source.priority>=w->source.priority &&
         r->source.thread_nr!=w->source.thread_nr) 
      {
        // the guard of w_prime follows from rf; with rfi
        // optimisation such as the previous write_symbol_primed
        // it would even be wrong to add this guard
        cond=
          implies_exprt(
            and_exprt(r->guard, w->guard, ws1, rf),
            last(r, w));
      }
      else if(c_it.first.second==w && !ws2.is_false() &&
              r->source.priority>=w_prime->source.priority &&
              r->source.thread_nr!=w_prime->source.thread_nr)
      {
        // the guard of w follows from rf; with rfi
        // optimisation such as the previous write_symbol_primed
        // it would even be wrong to add this guard
        cond=
          implies_exprt(
            and_exprt(r->guard, w_prime->guard, ws2, rf),
            last(r, w_prime));
      }

      if(cond.is_not_nil())
        add_constraint(equation, cond, "fr-irq", r->source);
    }
  }
}

/*******************************************************************\

Function: memory_model_interruptt::last

  Inputs:

 Outputs:

 Purpose: compute a before constraint from the last event of the thread 
          which the from event is in to the to event

\*******************************************************************/

exprt memory_model_interruptt::last(const event_it &from, const event_it &to)
{
  const event_listt &events=per_thread_map[from->source.thread_nr];
  exprt::operandst pty_operands;
  pty_operands.reserve(1);

  event_listt::const_iterator e_it=--events.end();
  assert(std::find(events.begin(), events.end(), from)!=events.end());

  while(from!=*e_it)
  {
    if((*e_it)->is_shared_write() ||
       (*e_it)->is_shared_read() ||
       (*e_it)->is_spawn())
    {
      pty_operands.push_back(before(*e_it, to));
      break;
    }
    --e_it;
  }

  return conjunction(pty_operands);
}
