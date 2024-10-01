/*******************************************************************\

Module: Memory model for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Memory model for partial order concurrency

#include "memory_model_tso.h"

#include <util/std_expr.h>
#include <util/simplify_expr.h>

void memory_model_tsot::
operator()(symex_target_equationt &equation, message_handlert &message_handler)
{
  messaget log{message_handler};
  log.statistics() << "Adding TSO constraints" << messaget::eom;

  build_event_lists(equation, message_handler);
  build_clock_type();

  read_from(equation);
  write_serialization_external(equation);
  program_order(equation);
#ifndef CPROVER_MEMORY_MODEL_SUP_CLOCK
  from_read(equation);
#endif
}

exprt memory_model_tsot::before(event_it e1, event_it e2)
{
  return partial_order_concurrencyt::before(
    e1, e2, AX_SC_PER_LOCATION | AX_PROPAGATION);
}

bool memory_model_tsot::program_order_is_relaxed(
  partial_order_concurrencyt::event_it e1,
  partial_order_concurrencyt::event_it e2) const
{
  PRECONDITION(e1->is_shared_read() || e1->is_shared_write());
  PRECONDITION(e2->is_shared_read() || e2->is_shared_write());

  // no po relaxation within atomic sections
  if(e1->atomic_section_id!=0 &&
     e1->atomic_section_id==e2->atomic_section_id)
    return false;

  // write to read program order is relaxed
  return e1->is_shared_write() && e2->is_shared_read();
}

void memory_model_tsot::program_order(
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

    for(event_listt::const_iterator
        e_it=events.begin();
        e_it!=events.end();
        e_it++)
    {
      if((*e_it)->is_memory_barrier())
        continue;

      event_listt::const_iterator next=e_it;
      ++next;

      exprt mb_guard_r = false_exprt();
      exprt mb_guard_w = false_exprt();

      for(event_listt::const_iterator
          e_it2=next;
          e_it2!=events.end();
          e_it2++)
      {
        if(((*e_it)->is_spawn() && !(*e_it2)->is_memory_barrier()) ||
           (*e_it2)->is_spawn())
        {
          add_constraint(
            equation,
            before(*e_it, *e_it2),
            "po",
            (*e_it)->source);

          if((*e_it2)->is_spawn())
            break;
          else
            continue;
        }

        if((*e_it2)->is_memory_barrier())
        {
          const codet &code = (*e_it2)->source.pc->code();

          if((*e_it)->is_shared_read() &&
             !code.get_bool(ID_RRfence) &&
             !code.get_bool(ID_RWfence))
            continue;
          else if((*e_it)->is_shared_write() &&
             !code.get_bool(ID_WRfence) &&
             !code.get_bool(ID_WWfence))
            continue;

          if(code.get_bool(ID_RRfence) ||
             code.get_bool(ID_WRfence))
            mb_guard_r=or_exprt(mb_guard_r, (*e_it2)->guard);

          if(code.get_bool(ID_RWfence) ||
             code.get_bool(ID_WWfence))
            mb_guard_w=or_exprt(mb_guard_w, (*e_it2)->guard);

          continue;
        }

        exprt cond=true_exprt();
        exprt ordering=nil_exprt();

        if(address(*e_it)==address(*e_it2))
        {
          ordering=partial_order_concurrencyt::before(
            *e_it, *e_it2, AX_SC_PER_LOCATION);
        }
        else if(program_order_is_relaxed(*e_it, *e_it2))
        {
          if((*e_it2)->is_shared_read())
            cond=mb_guard_r;
          else
            cond=mb_guard_w;

          simplify(cond, ns);
        }

        if(!cond.is_false())
        {
          if(ordering.is_nil())
            ordering=partial_order_concurrencyt::before(
              *e_it, *e_it2, AX_PROPAGATION);

          add_constraint(
            equation,
            implies_exprt(cond, ordering),
            "po",
            (*e_it)->source);
        }
      }
    }
  }
}

void memory_model_tsot::write_serialization_external(
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
#if 0
    std::size_t w_w_data_race_property_counter = 0;
#endif
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

        // ws is a total order, no two elements in distinct atomic sections have
        // the same rank
        DATA_INVARIANT(
          (*w_it1)->atomic_section_id == 0 ||
          (*w_it1)->atomic_section_id != (*w_it2)->atomic_section_id,
          "non-atomic writes in distinct threads cannot belong to the same "
          "atomic section");

        if((*w_it1)->atomic_section_id != 0 && (*w_it2)->atomic_section_id != 0)
        {
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
        else
        {
#if 0
           notequal_exprt ne{clock(*w_it1, axiomt::AX_PROPAGATION), clock(*w_it2, axiomt::AX_PROPAGATION)};
          equation.assertion(
            simplify_expr(and_exprt{(*w_it1)->guard, (*w_it2)->guard}, ns),
            ne,
            id2string(a_it->first) + ".w_w_data_race." + std::to_string(++w_w_data_race_property_counter),
            "write/write data race on " + id2string(a_it->first),
            (*w_it1)->source);
#endif
        }
      }
    }
  }
}
