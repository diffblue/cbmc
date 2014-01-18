/*******************************************************************\

Module: Memory model for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#include <util/std_expr.h>
#include <util/simplify_expr.h>

#include "memory_model_tso.h"

/*******************************************************************\

Function: memory_model_tsot::operator()

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_tsot::operator()(symex_target_equationt &equation)
{
  print(8, "Adding TSO constraints");

  build_event_lists(equation);
  build_clock_type(equation);
  
  read_from(equation);
  write_serialization_external(equation);
  program_order(equation);
#ifndef CPROVER_MEMORY_MODEL_SUP_CLOCK
  from_read(equation);
#endif
}

/*******************************************************************\

Function: memory_model_tsot::before

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

exprt memory_model_tsot::before(event_it e1, event_it e2)
{
  return partial_order_concurrencyt::before(
    e1, e2, AX_SC_PER_LOCATION | AX_PROPAGATION);
}

/*******************************************************************\

Function: memory_model_tsot::program_order_is_relaxed

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool memory_model_tsot::program_order_is_relaxed(
  partial_order_concurrencyt::event_it e1,
  partial_order_concurrencyt::event_it e2) const
{
  assert(is_shared_read(e1) || is_shared_write(e1));
  assert(is_shared_read(e2) || is_shared_write(e2));

  // no po relaxation within atomic sections
  if(e1->atomic_section_id!=0 &&
     e1->atomic_section_id==e2->atomic_section_id)
    return false;

  // write to read program order is relaxed
  return is_shared_write(e1) && is_shared_read(e2);
}

/*******************************************************************\

Function: memory_model_tsot::program_order

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
      if(is_memory_barrier(*e_it))
        continue;

      event_listt::const_iterator next=e_it;
      ++next;

      exprt mb_guard_r, mb_guard_w;
      mb_guard_r.make_false();
      mb_guard_w.make_false();

      for(event_listt::const_iterator
          e_it2=next;
          e_it2!=events.end();
          e_it2++)
      {
        if((is_spawn(*e_it) && !is_memory_barrier(*e_it2)) ||
           is_spawn(*e_it2))
        {
          add_constraint(
            equation,
            before(*e_it, *e_it2),
            "po",
            (*e_it)->source);

          if(is_spawn(*e_it2))
            break;
          else
            continue;
        }

        if(is_memory_barrier(*e_it2))
        {
          const codet &code=to_code((*e_it2)->source.pc->code);

          if(is_shared_read(*e_it) &&
             !code.get_bool(ID_RRfence) &&
             !code.get_bool(ID_RWfence))
            continue;
          else if(is_shared_write(*e_it) &&
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
          if(is_shared_read(*e_it2))
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

