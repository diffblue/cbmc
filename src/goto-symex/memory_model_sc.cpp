/*******************************************************************\

Module: Memory model for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#include <util/std_expr.h>
#include <util/i2string.h>

#include "memory_model_sc.h"

/*******************************************************************\

Function: memory_model_sct::operator()

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_sct::operator()(symex_target_equationt &equation)
{
  print(8, "Adding SC constraints");

  build_event_lists(equation);
  build_clock_type(equation);
  
  read_from(equation);
  write_serialization_internal(equation);
  write_serialization_external(equation);
  program_order(equation);
  from_read(equation);
}

/*******************************************************************\

Function: memory_model_sct::program_order

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_sct::program_order(
  symex_target_equationt &equation)
{
  // this orders the events within a thread

  per_thread_mapt per_thread_map;
  
  for(eventst::const_iterator
      e_it=equation.SSA_steps.begin();
      e_it!=equation.SSA_steps.end();
      e_it++)
  {
    // concurreny-related?
    if(!is_shared_read(e_it) &&
       !is_shared_write(e_it) &&
       !is_spawn(e_it)) continue;

    per_thread_map[e_it->source.thread_nr].push_back(e_it);
  }
  
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
      if(previous==equation.SSA_steps.end())
      {
        // first one?
        previous=*e_it;
        continue;
      }

      equation.constraint(
        true_exprt(),
        before(previous, *e_it),
        "po",
        (*e_it)->source);

      previous=*e_it;
    }
  }

  // thread spawn: the spawn precedes the first
  // instruction of the new thread in program order
  
  for(per_thread_mapt::const_iterator
      t_it=per_thread_map.begin();
      t_it!=per_thread_map.end();
      t_it++)
  {
    per_thread_mapt::const_iterator next_thread=t_it;
    next_thread++;
    if(next_thread==per_thread_map.end()) continue;
    if(next_thread->second.empty()) continue;

    const event_listt &events=t_it->second;
    
    // iterate over events in the thread
    
    for(event_listt::const_iterator
        e_it=events.begin();
        e_it!=events.end();
        e_it++)
    {
      if(is_spawn(*e_it))
      {
        equation.constraint(
          true_exprt(),
          before(*e_it, next_thread->second.front()),
          "thread-spawn",
          (*e_it)->source);
      }
    }    
  }
}

/*******************************************************************\

Function: memory_model_sct::write_serialization_internal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_sct::write_serialization_internal(
  symex_target_equationt &equation)
{
  for(address_mapt::const_iterator
      a_it=address_map.begin();
      a_it!=address_map.end();
      a_it++)
  {
    const a_rect &a_rec=a_it->second;
    
    for(event_listt::const_iterator
        w_it=a_rec.writes.begin();
        w_it!=a_rec.writes.end();
        ++w_it)
    {
      //const eventt &write_event=**w_it;

      #if 0
      if(reads.find(w_evt2.address)!=reads.end())
      {
        assert(!mr.empty() || w_evt2.guard.is_true());
        equal_exprt eq(write_symbol_primed(w_evt2),
            w_evt2.guard.is_true() ?
            // value' equals value
            w_evt2.value :
            // value' equals preceding write if guard is false
            if_exprt(w_evt2.guard.as_expr(),
              w_evt2.value,
              write_symbol_primed(*mr.back())));

        poc.add_constraint(eq, guardt(), w_evt2.source, "ws-preceding");
      }
      #endif
    }
  }
}

/*******************************************************************\

Function: memory_model_sct::write_serialization_external

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
        equation.constraint(
          true_exprt(),
          implies_exprt(s, before(*w_it1, *w_it2)),
          "ws-ext",
          (*w_it1)->source);

        equation.constraint(
          true_exprt(),
          implies_exprt(not_exprt(s), before(*w_it2, *w_it1)),
          "ws-ext",
          (*w_it1)->source);
      }
    }
  }
}

/*******************************************************************\

Function: memory_model_sct::from_read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
        exprt ws;
        
        if(po(*w_prime, *w))
          ws=true_exprt(); // true on SC only!
        else
          ws=before(*w_prime, *w);

        // smells like cubic
        for(choice_symbolst::const_iterator
            c_it=choice_symbols.begin();
            c_it!=choice_symbols.end();
            c_it++)
        {
          event_it r=c_it->first.first;
        
          if(c_it->first.second!=*w_prime)
            continue;

          exprt rf=c_it->second;
          exprt fr=before(r, *w);
          
          exprt cond=
            implies_exprt(
              and_exprt(r->guard, (*w_prime)->guard, ws, rf),
              fr);
          
          equation.constraint(
            true_exprt(), cond, "fr", r->source);
        }
        
      }
    }
  }

  #if 0
  // from-read: (w', w) in ws and (w', r) in rf -> (r, w) in fr
  // uniproc and ghb orders are guaranteed to be in sync via the
  // underlying orders rf and ws

  for(partial_order_concurrencyt::adj_matrixt::const_iterator
      w_prime=ws.begin();
      w_prime!=ws.end();
      ++w_prime)
  {
    partial_order_concurrencyt::adj_matrixt::const_iterator w_prime_rf=
      rf.find(w_prime->first);
    if(w_prime_rf==rf.end())
      continue;

    for(std::map<evtt const*, exprt>::const_iterator
        r=w_prime_rf->second.begin();
        r!=w_prime_rf->second.end();
        ++r)
    {
      const evtt &r_evt=*(r->first);

      for(std::map<evtt const*, exprt>::const_iterator
          w=w_prime->second.begin();
          w!=w_prime->second.end();
          ++w)
      {
        const evtt &w_evt=*(w->first);

        const evtt* f_e=poc.first_of(r_evt, w_evt);
        bool is_fri=f_e!=0;
        // TODO: make sure the following skips are ok even if guard does not
        // evaluate to true
        // internal fr only backward or to first successor (in po)
        if(check==AC_GHB)
        {
          numbered_evtst::const_iterator w_entry=
            poc.get_thread(w_evt).find(w_evt);
          assert(w_entry!=poc.get_thread(w_evt).end());
          numbered_evtst::const_iterator r_entry=
            poc.get_thread(w_evt).find(r_evt);

          if(r_entry!=poc.get_thread(w_evt).end() &&
              r_entry<w_entry)
          {
            bool is_next=true;
            for(++r_entry; r_entry!=w_entry && is_next; ++r_entry)
              is_next&=(*r_entry)->direction!=evtt::D_WRITE ||
                (*r_entry)->address!=w_evt.address;
            if(!is_next)
              continue;
          }
        }
        // no internal forward fr, these are redundant with po-loc
        else if(check==AC_UNIPROC && is_fri && f_e==&r_evt)
          continue;

        and_exprt a(and_exprt(r->second, w->second),
            and_exprt(w_evt.guard.as_expr(), r_evt.guard.as_expr()));
        poc.add_partial_order_constraint(check, "fr", r_evt, w_evt, a);
        // read-to-write edge
        std::pair<std::map<evtt const*, exprt>::iterator, bool> fr_map_entry=
          fr[&r_evt].insert(std::make_pair(&w_evt, a));
        if(!fr_map_entry.second)
        {
          or_exprt o(fr_map_entry.first->second, a);
          fr_map_entry.first->second.swap(o);
        }
      }
    }
  }
  #endif
}


