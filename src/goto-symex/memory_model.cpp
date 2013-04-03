/*******************************************************************\

Module: Memory model for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#include <std_expr.h>
#include <i2string.h>

#include "memory_model.h"

/*******************************************************************\

Function: memory_model_baset::~memory_model_baset

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

memory_model_baset::memory_model_baset():var_cnt(0)
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

Function: memory_model_baset::build_event_lists

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_baset::build_event_lists(
  symex_target_equationt &equation)
{
  // a per-thread counter
  std::map<unsigned, unsigned> counter;

  for(eventst::const_iterator
      e_it=equation.SSA_steps.begin();
      e_it!=equation.SSA_steps.end();
      e_it++)
  {
    const eventt &event=*e_it;
    unsigned thread_nr=event.source.thread_nr;    
    
    if(event.is_read() || event.is_assignment())
    {
      a_rect &a_rec=address_map[address(event)];
    
      if(event.is_read())
        a_rec.reads.push_back(&event);
      else if(event.is_assignment())
        a_rec.writes.push_back(&event);

      // maps an event id to a per-thread counter
      unsigned cnt=counter[thread_nr]++;
      numbering[&event]=cnt;
    }
  }
}

/*******************************************************************\

Function: memory_model_baset::po

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

bool memory_model_baset::po(const eventt &e1, const eventt &e2)
{
  // within same thread
  if(e1.source.thread_nr==e2.source.thread_nr)
    return numbering[&e1]<numbering[&e2];
  else
  {
    // in general un-ordered, with exception of thread-spawning
    return false;
  }
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
      const eventt &read_event=**r_it;
      
      exprt::operandst rf_some_operands;
      rf_some_operands.reserve(a_rec.writes.size());

      // this is quadratic in #events per address
      for(event_listt::const_iterator
          w_it=a_rec.writes.begin();
          w_it!=a_rec.writes.end();
          ++w_it)
      {
        const eventt &write_event=**w_it;
        
        // rf cannot contradict program order
        if(po(read_event, write_event))
          continue; // contradicts po

        bool is_rfi=
          write_event.source.thread_nr==read_event.source.thread_nr;

        if(is_rfi)
        {
          // We only read from the most recent write of the same thread.
          // Extra wsi constraints ensure that even a
          // write with guard false will have the proper value.

          numberingt::const_iterator w_entry=
            numbering.find(&write_event);
          assert(w_entry!=numbering.end());

          numberingt::const_iterator r_entry=
            numbering.find(&read_event);
          assert(r_entry!=numbering.end());

          assert(w_entry->second<r_entry->second); // otherwise contradicts po

          bool is_most_recent=true;
          for(++w_entry; w_entry!=r_entry && is_most_recent; ++w_entry)
            is_most_recent&=w_entry->first->is_assignment() ||
                            address(*w_entry->first)!=address(read_event);
          if(!is_most_recent)
            continue;
        }

        symbol_exprt s=nondet_bool_symbol("rf");
        
        // record the symbol
        choice_symbols[
          std::pair<irep_idt, irep_idt>(id(read_event), id(write_event))]=s;

        // We rely on the fact that there is at least
        // one write event that has guard 'true'.
        implies_exprt read_from(s,
            and_exprt((is_rfi ? true_exprt() : write_event.guard),
              equal_exprt(read_event.ssa_lhs, write_event.ssa_lhs)));

        equation.constraint(
          true_exprt(), read_from, is_rfi?"rfi":"rf", read_event.source);

        rf_some_operands.push_back(s);
      }
      
      if(rf_some_operands.empty())
        continue; // don't add blank constraints

      // value equals the one of some write
      or_exprt rf_some;
      rf_some.operands().swap(rf_some_operands);

      equation.constraint(
        read_event.guard, rf_some, "rf-some", read_event.source);
    }
  }
}

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
    const eventt &event=*e_it;
    per_thread_map[event.source.thread_nr].push_back(&event);
  }
  
  // iterate over threads

  for(per_thread_mapt::const_iterator
      t_it=per_thread_map.begin();
      t_it!=per_thread_map.end();
      t_it++)
  {
    const event_listt &events=t_it->second;
    
    // iterate over events in the thread
    
    const eventt *previous=NULL;
    
    for(event_listt::const_iterator
        e_it=events.begin();
        e_it!=events.end();
        e_it++)
    {
      const eventt &event=**e_it;

      if(!event.is_read() &&
         !event.is_assignment() &&
         !event.is_spawn()) continue;

      if(previous==NULL)
      {
        // first one?
        previous=&event;
        continue;
      }

      equation.constraint(
        true_exprt(),
        po_constraint(*previous, event),
        "po",
        event.source);

      #if 0
      // check for thread spawn -- in po with last event before spawn
      if(e.source.thread_nr!=(*pred)->source.thread_nr)
      {
        assert(e.source.thread_nr>(*pred)->source.thread_nr);

        poc.add_partial_order_constraint(
            AC_GHB, "thread-spawn", **pred, e, true_exprt());
        po[AC_GHB][*pred][&e].make_true();
      }
      #endif

      previous=&event;
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
      const eventt &write_event1=**w_it1;

      event_listt::const_iterator next=w_it1;
      ++next;

      for(event_listt::const_iterator w_it2=next;
          w_it2!=a_rec.writes.end();
          ++w_it2)
      {
        const eventt &write_event2=**w_it2;
        
        // external?
        if(write_event1.source.thread_nr==
           write_event2.source.thread_nr)
          continue;

        // ws is a total order, no two elements have the same rank
        // s -> w_evt1 before w_evt2; !s -> w_evt2 before w_evt1

        symbol_exprt s=nondet_bool_symbol("ws-ext");

        // write-to-write edge
        equation.constraint(
          true_exprt(),
          implies_exprt(s, po_constraint(write_event1, write_event2)),
          "ws-ext",
          write_event1.source);

        equation.constraint(
          true_exprt(),
          implies_exprt(not_exprt(s), po_constraint(write_event2, write_event1)),
          "ws-ext",
          write_event1.source);
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
  // uniproc and ghb orders are guaranteed to be in sync via the
  // underlying orders rf and ws

  #if 0
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

