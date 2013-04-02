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

    if(event.is_read())
      reads.push_back(&event);
    else if(event.is_assignment())
      writes.push_back(&event);

    unsigned cnt=counter[thread_nr]++;
    numbering[id(event)]=cnt;
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
  
  for(event_listt::const_iterator
      r_it=reads.begin();
      r_it!=reads.end();
      r_it++)
  {
    const eventt &read_event=**r_it;
    
    exprt::operandst rf_some_operands;
    rf_some_operands.reserve(writes.size());

    // this is quadratic
    for(event_listt::const_iterator
        w_it=writes.begin();
        w_it!=writes.end();
        ++w_it)
    {
      const eventt &write_event=**w_it;
      
      // check that this is the same address
      if(id(read_event)!=id(write_event))
        continue; // different address
      
      // rf cannot contradict program order
      if(po(read_event, write_event))
        continue; // contradicts po

      bool is_rfi=
        write_event.source.thread_nr==read_event.source.thread_nr;

      if(is_rfi)
      {
        // only read from the most recent write, extra wsi constraints ensure
        // that even a write with guard false will have the proper value
        #if 0
        numbered_evtst::const_iterator w_entry=
          poc.get_thread(r_evt).find(w_evt);
        assert(w_entry!=poc.get_thread(r_evt).end());
        numbered_evtst::const_iterator r_entry=
          poc.get_thread(r_evt).find(r_evt);
        assert(r_entry!=poc.get_thread(r_evt).end());

        assert(w_entry<r_entry);
        bool is_most_recent=true;
        for(++w_entry; w_entry!=r_entry && is_most_recent; ++w_entry)
          is_most_recent&=(*w_entry)->direction!=evtt::D_WRITE ||
            (*w_entry)->address!=r_evt.address;
        if(!is_most_recent)
          continue;
        #endif
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
  #if 0
  assert(thread.begin()!=thread.end());

  partial_order_concurrencyt::per_address_mapt most_recent_evt;
  typedef std::list<numbered_evtst::const_iterator> chaint;
  typedef std::list<chaint> root_chainst;

  numbered_evtst::const_iterator pred=thread.begin();
  assert((*pred)->direction==evtt::D_READ ||
         (*pred)->direction==evtt::D_WRITE);
  most_recent_evt[(*pred)->address].push_back(*pred);
  root_chainst root_chains(1, chaint(1, pred));

  for(numbered_evtst::const_iterator e_it=++(thread.begin());
      e_it!=thread.end();
      ++e_it)
  {
    const evtt &e=**e_it;

    // check e for non-barrier event; pred updated below, hence pred is always
    // a non-barrier
    if(e.direction!=evtt::D_READ && e.direction!=evtt::D_WRITE)
      continue;

    // check for thread spawn -- in po with last event before spawn
    if(e.source.thread_nr!=(*pred)->source.thread_nr)
    {
      assert(e.source.thread_nr>(*pred)->source.thread_nr);

      poc.add_partial_order_constraint(
          AC_GHB, "thread-spawn", **pred, e, true_exprt());
      po[AC_GHB][*pred][&e].make_true();
    }

    // uniproc -- program order per address
    if(uses_check(AC_UNIPROC))
    {
      partial_order_concurrencyt::per_valuet &mr=most_recent_evt[e.address];
      if(!mr.empty())
      {
        poc.add_partial_order_constraint(
            AC_UNIPROC, "uniproc", *mr.back(), e, true_exprt());
        po[AC_UNIPROC][mr.back()][&e].make_true();
      }
      mr.push_back(&e);
    }

    // program order
    bool extended_chain=false;
    for(root_chainst::iterator r_it=root_chains.begin();
        r_it!=root_chains.end();
        ++r_it)
    {
      // should be const_reverse_iterator, but some STLs are buggy
      for(chaint::reverse_iterator cand=r_it->rbegin();
          cand!=r_it->rend();
          ++cand)
      {
        const evtt &c_e=***cand;
        // dependencies
        if(!po_is_relaxed(poc, c_e, e))
        {
          if(uses_check(AC_THINAIR))
          {
            poc.add_partial_order_constraint(
                AC_THINAIR, "thin-air", c_e, e, true_exprt());
            po[AC_THINAIR][&c_e][&e].make_true();
          }

          poc.add_partial_order_constraint(
              AC_GHB, "po", c_e, e, true_exprt());
          po[AC_GHB][&c_e][&e].make_true();

          if(cand==r_it->rbegin())
          {
            r_it->push_back(e_it);
            extended_chain=true;
          }
          break;
        }
      }
    }
    if(!extended_chain)
      root_chains.push_back(chaint(1, e_it));

    pred=e_it;
  }
  #endif
}

/*******************************************************************\

Function: write_symbol_primed

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
static exprt write_symbol_primed(
    const partial_order_concurrencyt::evtt &evt)
{
  assert(evt.direction==partial_order_concurrencyt::evtt::D_WRITE);

  if(evt.value.id()!=ID_symbol)
  {
    // initialisation
    assert(evt.guard.is_true());
    return evt.value;
  }

  const std::string name=
    id2string(to_symbol_expr(evt.value).get_identifier()) + "$val";

  return symbol_exprt(name, evt.value.type());
}
#endif

/*******************************************************************\

Function: memory_model_sct::write_serialization_internal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_sct::write_serialization_internal(
  symex_target_equationt &equation)
{
  for(event_listt::const_iterator w_it=writes.begin();
      w_it!=writes.end();
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

/*******************************************************************\

Function: memory_model_sct::write_serialization_external

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_sct::write_serialization_external(
  symex_target_equationt &equation)
{
  for(event_listt::const_iterator
      w_it1=writes.begin();
      w_it1!=writes.end();
      ++w_it1)
  {
    const eventt &write_event1=**w_it1;

    event_listt::const_iterator next=w_it1;
    ++next;

    for(event_listt::const_iterator w_it2=next;
        w_it2!=writes.end();
        ++w_it2)
    {
      const eventt &write_event2=**w_it2;

      // ws is a total order, no two elements have the same rank
      // s -> w_evt1 before w_evt2; !s -> w_evt2 before w_evt1

      #if 0
      //const evtt* f_e=poc.first_of(w_evt1, w_evt2);
      exprt s;
      if(!f_e)
        s=poc.fresh_nondet_bool();
      else
        s.make_bool(f_e==&w_evt1);

      // write-to-write edge
      //ws[AC_GHB][&w_evt1].insert(std::make_pair(&w_evt2, s));
      //ws[AC_GHB][&w_evt2].insert(std::make_pair(&w_evt1, not_exprt(s)));

      poc.add_partial_order_constraint(AC_GHB, "ws", w_evt1, w_evt2, s);
      poc.add_partial_order_constraint(AC_GHB, "ws", w_evt2, w_evt1,
          not_exprt(s));

      if(uses_check(AC_UNIPROC))
      {
        poc.add_partial_order_constraint(AC_UNIPROC, "ws", w_evt1, w_evt2, s);
        poc.add_partial_order_constraint(AC_UNIPROC, "ws", w_evt2, w_evt1,
            not_exprt(s));
        // write-to-write edge
        ws[AC_UNIPROC][&w_evt1].insert(std::make_pair(&w_evt2, s));
        ws[AC_UNIPROC][&w_evt2].insert(std::make_pair(&w_evt1, not_exprt(s)));
      }
      #endif
    }
  }
}

/*******************************************************************\

Function: memory_model_baset::add_from_read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
void memory_model_baset::add_from_read(
    partial_order_concurrencyt &poc,
    const partial_order_concurrencyt::acyclict check,
    const partial_order_concurrencyt::adj_matrixt &rf,
    const partial_order_concurrencyt::adj_matrixt &ws,
    partial_order_concurrencyt::adj_matrixt &fr) const
{
  assert(check==AC_GHB || check==AC_UNIPROC);

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
}

#endif
