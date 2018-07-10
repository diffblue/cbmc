/*******************************************************************\

Module: Memory model for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Memory model for partial order concurrency

#include "memory_model_sc.h"

#include <util/std_expr.h>

void memory_model_sct::operator()(symex_target_equationt &equation)
{
  statistics() << "Adding SC constraints" << eom;

  build_event_lists(equation);
  build_clock_type();

  read_from(equation);
  write_serialization_external(equation);
  program_order(equation);
  from_read(equation);
}

exprt memory_model_sct::before(event_it e1, event_it e2)
{
  return partial_order_concurrencyt::before(
    e1, e2, AX_PROPAGATION);
}

bool memory_model_sct::program_order_is_relaxed(
  partial_order_concurrencyt::event_it e1,
  partial_order_concurrencyt::event_it e2) const
{
  PRECONDITION(e1->is_shared_read() || e1->is_shared_write());
  PRECONDITION(e2->is_shared_read() || e2->is_shared_write());

  return false;
}

void memory_model_sct::build_per_thread_map(
  const symex_target_equationt &equation,
  per_thread_mapt &dest) const
{
  // this orders the events within a thread

  for(eventst::const_iterator
      e_it=equation.SSA_steps.begin();
      e_it!=equation.SSA_steps.end();
      e_it++)
  {
    // concurrency-related?
    if(!e_it->is_shared_read() &&
       !e_it->is_shared_write() &&
       !e_it->is_spawn() &&
       !e_it->is_memory_barrier()) continue;

    dest[e_it->source.thread_nr].push_back(e_it);
  }
}

void memory_model_sct::thread_spawn(
  symex_target_equationt &equation,
  const per_thread_mapt &per_thread_map)
{
  // thread spawn: the spawn precedes the first
  // instruction of the new thread in program order

  unsigned next_thread_id=0;
  for(eventst::const_iterator
      e_it=equation.SSA_steps.begin();
      e_it!=equation.SSA_steps.end();
      e_it++)
  {
    if(e_it->is_spawn())
    {
      per_thread_mapt::const_iterator next_thread=
        per_thread_map.find(++next_thread_id);
      if(next_thread==per_thread_map.end())
        continue;

      // add a constraint for all events,
      // considering regression/cbmc-concurrency/pthread_create_tso1
      for(event_listt::const_iterator
          n_it=next_thread->second.begin();
          n_it!=next_thread->second.end();
          n_it++)
      {
        if(!(*n_it)->is_memory_barrier())
          add_constraint(
            equation,
            before(e_it, *n_it),
            "thread-spawn",
            e_it->source);
      }
    }
  }
}

#if 0
void memory_model_sct::thread_spawn(
  symex_target_equationt &equation,
  const per_thread_mapt &per_thread_map)
{
  // thread spawn: the spawn precedes the first
  // instruction of the new thread in program order

  unsigned next_thread_id=0;
  for(eventst::const_iterator
      e_it=equation.SSA_steps.begin();
      e_it!=equation.SSA_steps.end();
      e_it++)
  {
    if(is_spawn(e_it))
    {
      per_thread_mapt::const_iterator next_thread=
        per_thread_map.find(++next_thread_id);
      if(next_thread==per_thread_map.end())
        continue;

      // For SC and several weaker memory models a memory barrier
      // at the beginning of a thread can simply be ignored, because
      // we enforce program order in the thread-spawn constraint
      // anyway. Memory models with cumulative memory barriers
      // require explicit handling of these.
      event_listt::const_iterator n_it=next_thread->second.begin();
      for( ;
          n_it!=next_thread->second.end() &&
          (*n_it)->is_memory_barrier();
          ++n_it)
      {
      }

      if(n_it!=next_thread->second.end())
        add_constraint(
          equation,
          before(e_it, *n_it),
          "thread-spawn",
          e_it->source);
    }
  }
}
#endif

void memory_model_sct::program_order(
  symex_target_equationt &equation)
{
  per_thread_mapt per_thread_map;
  build_per_thread_map(equation, per_thread_map);

  thread_spawn(equation, per_thread_map);

  // iterate over threads

  for(per_thread_mapt::const_iterator
      t_it=per_thread_map.begin();
      t_it!=per_thread_map.end();
      t_it++)
  {
    const event_listt &events=t_it->second;

    // iterate over relevant events in the thread

    event_it previous=equation.SSA_steps.end();

    for(event_listt::const_iterator
        e_it=events.begin();
        e_it!=events.end();
        e_it++)
    {
      if((*e_it)->is_memory_barrier())
         continue;

      if(previous==equation.SSA_steps.end())
      {
        // first one?
        previous=*e_it;
        continue;
      }

      add_constraint(
        equation,
        before(previous, *e_it),
        "po",
        (*e_it)->source);

      previous=*e_it;
    }
  }
}

void memory_model_sct::write_serialization_external(
  symex_target_equationt &equation)
{
  for(address_mapt::const_iterator
      a_it=address_map.begin();
      a_it!=address_map.end();
      a_it++)
  {
    const a_rect &a_rec=a_it->second;

    // This is quadratic in the number of writes
    // per address. Perhaps some better encoding
    // based on 'places'?
    for(event_listt::const_iterator
        w_it1=a_rec.writes.begin();
        w_it1!=a_rec.writes.end();
        ++w_it1)
    {
      event_listt::const_iterator next=w_it1;
      ++next;

      for(event_listt::const_iterator w_it2=next;
          w_it2!=a_rec.writes.end();
          ++w_it2)
      {
        // external?
        if((*w_it1)->source.thread_nr==
           (*w_it2)->source.thread_nr)
          continue;

        // ws is a total order, no two elements have the same rank
        // s -> w_evt1 before w_evt2; !s -> w_evt2 before w_evt1

        symbol_exprt s=nondet_bool_symbol("ws-ext");

        // write-to-write edge
        add_constraint(
          equation,
          implies_exprt(s, before(*w_it1, *w_it2)),
          "ws-ext",
          (*w_it1)->source);

        add_constraint(
          equation,
          implies_exprt(not_exprt(s), before(*w_it2, *w_it1)),
          "ws-ext",
          (*w_it1)->source);
      }
    }
  }
}

void memory_model_sct::from_read(symex_target_equationt &equation)
{
  // from-read: (w', w) in ws and (w', r) in rf -> (r, w) in fr

  for(address_mapt::const_iterator
      a_it=address_map.begin();
      a_it!=address_map.end();
      a_it++)
  {
    const a_rect &a_rec=a_it->second;

    // This is quadratic in the number of writes per address.
    for(event_listt::const_iterator
        w_prime=a_rec.writes.begin();
        w_prime!=a_rec.writes.end();
        ++w_prime)
    {
      event_listt::const_iterator next=w_prime;
      ++next;

      for(event_listt::const_iterator w=next;
          w!=a_rec.writes.end();
          ++w)
      {
        exprt ws1, ws2;

        if(po(*w_prime, *w) &&
           !program_order_is_relaxed(*w_prime, *w))
        {
          ws1=true_exprt();
          ws2=false_exprt();
        }
        else if(po(*w, *w_prime) &&
                !program_order_is_relaxed(*w, *w_prime))
        {
          ws1=false_exprt();
          ws2=true_exprt();
        }
        else
        {
          ws1=before(*w_prime, *w);
          ws2=before(*w, *w_prime);
        }

        // smells like cubic
        for(choice_symbolst::const_iterator
            c_it=choice_symbols.begin();
            c_it!=choice_symbols.end();
            c_it++)
        {
          event_it r=c_it->first.first;
          exprt rf=c_it->second;
          exprt cond;
          cond.make_nil();

          if(c_it->first.second==*w_prime && !ws1.is_false())
          {
            exprt fr=before(r, *w);

            // the guard of w_prime follows from rf; with rfi
            // optimisation such as the previous write_symbol_primed
            // it would even be wrong to add this guard
            cond=
              implies_exprt(
                and_exprt(r->guard, (*w)->guard, ws1, rf),
                fr);
          }
          else if(c_it->first.second==*w && !ws2.is_false())
          {
            exprt fr=before(r, *w_prime);

            // the guard of w follows from rf; with rfi
            // optimisation such as the previous write_symbol_primed
            // it would even be wrong to add this guard
            cond=
              implies_exprt(
                and_exprt(r->guard, (*w_prime)->guard, ws2, rf),
                fr);
          }

          if(cond.is_not_nil())
            add_constraint(equation,
              cond, "fr", r->source);
        }
      }
    }
  }
}
