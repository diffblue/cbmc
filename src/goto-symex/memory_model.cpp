/*******************************************************************\

Module: Memory model for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#include <std_expr.h>

#define ENABLE_MM_MACROS
#include "memory_model.h"

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

Function: memory_model_baset::build_event_lists

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_baset::build_event_lists(symex_target_equationt &equation)
{
  for(eventst::const_iterator
      e_it=equation.SSA_steps.begin();
      e_it!=equation.SSA_steps.end();
      e_it++)
  {
    if(e_it->is_read())
      reads.push_back(&*e_it);
    else if(e_it->is_assignment())
      writes.push_back(&*e_it);
  }
}

/*******************************************************************\

Function: memory_model_sct::read_from

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_sct::operator()(symex_target_equationt &equation)
{
  read_from(equation);
}

/*******************************************************************\

Function: memory_model_sct::read_from

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_sct::read_from(symex_target_equationt &equation)
{
  // We iterate over all the reads, and
  // make them match a write.
  
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
      const eventt &w_evt=**w_it;

      #if 0
      // rf cannot contradict program order
      const evtt* f_e=poc.first_of(r_evt, w_evt);
      bool is_rfi=f_e!=0;
      if(is_rfi && f_e==&r_evt)
        continue; // contradicts po

      // only read from the most recent write, extra wsi constraints ensure
      // that even a write with guard false will have the proper value
      if(is_rfi)
      {
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
      }

      symbol_exprt s=poc.fresh_nondet_bool();
      implies_exprt read_from(s,
          and_exprt((is_rfi ? true_exprt() : w_evt.guard.as_expr()),
            equal_exprt(r_evt.value, write_symbol_primed(w_evt))));
      poc.add_constraint(read_from, guardt(), r_evt.source, is_rfi?"rfi":"rf");

      rf_some_operands.push_back(s);


      // uniproc, thinair and ghb orders are in sync via s
      if(uses_check(AC_UNIPROC))
      {
        poc.add_partial_order_constraint(AC_UNIPROC, "rf", w_evt, r_evt, s);
        // write-to-read edge
        rf[AC_UNIPROC][&w_evt].insert(std::make_pair(&r_evt, s));
      }
      if(uses_check(AC_THINAIR))
      {
        poc.add_partial_order_constraint(AC_THINAIR, "rf", w_evt, r_evt, s);
        // write-to-read edge
        rf[AC_THINAIR][&w_evt].insert(std::make_pair(&r_evt, s));
      }
      if(!rf_is_relaxed(w_evt, r_evt, is_rfi))
        poc.add_partial_order_constraint(AC_GHB, "rf", w_evt, r_evt, s);
      // write-to-read edge
      rf[AC_GHB][&w_evt].insert(std::make_pair(&r_evt, s));
      #endif
    }

    // value equals the one of some write
    or_exprt rf_some;
    rf_some.operands().swap(rf_some_operands);

    #if 0
    equation.constraint(
      rf_some, read_event.guard, read_event.source, "rf-at-least-one");
    #endif
  }
}

#if 0
/*******************************************************************\

Function: memory_model_baset::add_atomic_sections

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_baset::add_atomic_sections(
    partial_order_concurrencyt &poc) const
{
  for(int i=0; i<partial_order_concurrencyt::AC_N_AXIOMS; ++i)
  {
    partial_order_concurrencyt::acyclict c=
      static_cast<partial_order_concurrencyt::acyclict>(i);
    if(uses_check(c))
      poc.add_atomic_sections(c);
  }
}

/*******************************************************************\

Function: memory_model_baset::add_program_order

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_baset::add_program_order(
    partial_order_concurrencyt &poc,
    const numbered_evtst &thread,
    adj_matricest &po)
{
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
}

/*******************************************************************\

Function: write_symbol_primed

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: memory_model_baset::add_read_from

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_baset::add_read_from(
    partial_order_concurrencyt &poc,
    const partial_order_concurrencyt::per_valuet &reads,
    const partial_order_concurrencyt::per_valuet &writes,
    adj_matricest &rf)
{
  for(partial_order_concurrencyt::per_valuet::const_iterator
      it=reads.begin();
      it!=reads.end();
      ++it)
  {
    const evtt &r_evt=**it;
    exprt::operandst rf_some_operands;
    rf_some_operands.reserve(writes.size());

    for(partial_order_concurrencyt::per_valuet::const_iterator
        it2=writes.begin();
        it2!=writes.end();
        ++it2)
    {
      const evtt &w_evt=**it2;

      // rf cannot contradict program order
      const evtt* f_e=poc.first_of(r_evt, w_evt);
      bool is_rfi=f_e!=0;
      if(is_rfi && f_e==&r_evt)
        continue; // contradicts po

      // only read from the most recent write, extra wsi constraints ensure
      // that even a write with guard false will have the proper value
      if(is_rfi)
      {
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
      }

      symbol_exprt s=poc.fresh_nondet_bool();
      implies_exprt read_from(s,
          and_exprt((is_rfi ? true_exprt() : w_evt.guard.as_expr()),
            equal_exprt(r_evt.value, write_symbol_primed(w_evt))));
      poc.add_constraint(read_from, guardt(), r_evt.source, is_rfi?"rfi":"rf");

      rf_some_operands.push_back(s);


      // uniproc, thinair and ghb orders are in sync via s
      if(uses_check(AC_UNIPROC))
      {
        poc.add_partial_order_constraint(AC_UNIPROC, "rf", w_evt, r_evt, s);
        // write-to-read edge
        rf[AC_UNIPROC][&w_evt].insert(std::make_pair(&r_evt, s));
      }
      if(uses_check(AC_THINAIR))
      {
        poc.add_partial_order_constraint(AC_THINAIR, "rf", w_evt, r_evt, s);
        // write-to-read edge
        rf[AC_THINAIR][&w_evt].insert(std::make_pair(&r_evt, s));
      }
      if(!rf_is_relaxed(w_evt, r_evt, is_rfi))
        poc.add_partial_order_constraint(AC_GHB, "rf", w_evt, r_evt, s);
      // write-to-read edge
      rf[AC_GHB][&w_evt].insert(std::make_pair(&r_evt, s));
    }

    // value equals one of some write
    or_exprt rf_some;
    rf_some.operands().swap(rf_some_operands);
    poc.add_constraint(rf_some, r_evt.guard, r_evt.source, "rf-at-least-one");
  }
}

/*******************************************************************\

Function: memory_model_baset::add_write_serialisation_internal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_baset::add_write_serialisation_internal(
    partial_order_concurrencyt &poc,
    const numbered_evtst &thread,
    const partial_order_concurrencyt::per_address_mapt &reads,
    adj_matricest &ws) const
{
  // we include wsi in ppo and only add extra constraints and the edge to the
  // graph here
  partial_order_concurrencyt::per_address_mapt most_recent_evt;

  for(numbered_evtst::const_iterator w_it=thread.begin();
      w_it!=thread.end();
      ++w_it)
  {
    if((*w_it)->direction!=evtt::D_WRITE)
      continue;

    const evtt &w_evt2=**w_it;

    partial_order_concurrencyt::per_valuet &mr=most_recent_evt[w_evt2.address];
    if(!mr.empty())
    {
      /*
      const evtt &w_evt1=*mr.back();

      // uniproc and ghb orders are guaranteed to be in sync
      if(uses_check(AC_UNIPROC))
        // write-to-write edge
        ws[AC_UNIPROC][&w_evt1].insert(std::make_pair(&w_evt2, true_exprt()));

      // write-to-write edge
      ws[AC_GHB][&w_evt1].insert(std::make_pair(&w_evt2, true_exprt()));

      // PLDI requires acyclicity of writes and fences
      if(uses_check(AC_PPC_WS_FENCE))
        poc.add_partial_order_constraint(AC_PPC_WS_FENCE, "ws",
            w_evt1, w_evt2, true_exprt());
      */
    }

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

    mr.push_back(&w_evt2);
  }
}

/*******************************************************************\

Function: memory_model_baset::add_write_serialisation_external

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_baset::add_write_serialisation_external(
    partial_order_concurrencyt &poc,
    const partial_order_concurrencyt::per_valuet &writes,
    adj_matricest &ws) const
{
  for(partial_order_concurrencyt::per_valuet::const_iterator
      it=writes.begin();
      it!=writes.end();
      ++it)
  {
    const evtt &w_evt1=**it;

    partial_order_concurrencyt::per_valuet::const_iterator next=it;
    ++next;
    for(partial_order_concurrencyt::per_valuet::const_iterator
        it2=next;
        it2!=writes.end();
        ++it2)
    {
      const evtt &w_evt2=**it2;

      /*
      // only wse here
      if(poc.first_of(w_evt1, w_evt2)!=0)
        continue;
        */

      // ws is a total order, no two elements have the same rank
      // s -> w_evt1 before w_evt2; !s -> w_evt2 before w_evt1
      const evtt* f_e=poc.first_of(w_evt1, w_evt2);
      exprt s;
      if(!f_e)
        s=poc.fresh_nondet_bool();
      else
        s.make_bool(f_e==&w_evt1);

      // write-to-write edge
      ws[AC_GHB][&w_evt1].insert(std::make_pair(&w_evt2, s));
      ws[AC_GHB][&w_evt2].insert(std::make_pair(&w_evt1, not_exprt(s)));

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

      // PLDI requires acyclicity of writes and fences
      if(uses_check(AC_PPC_WS_FENCE))
      {
        poc.add_partial_order_constraint(AC_PPC_WS_FENCE, "ws",
            w_evt1, w_evt2, s);
        poc.add_partial_order_constraint(AC_PPC_WS_FENCE, "ws",
            w_evt2, w_evt1, not_exprt(s));
      }
    }
  }
}

/*******************************************************************\

Function: memory_model_baset::add_from_read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: memory_model_baset::add_from_read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_baset::add_from_read(
    partial_order_concurrencyt &poc,
    const adj_matricest &rf,
    const adj_matricest &ws,
    adj_matricest &fr) const
{
  add_from_read(poc, AC_GHB, rf[AC_GHB], ws[AC_GHB], fr[AC_GHB]);
  if(uses_check(AC_UNIPROC))
    add_from_read(poc, AC_UNIPROC,
        rf[AC_UNIPROC], ws[AC_UNIPROC], fr[AC_UNIPROC]);
}

/*******************************************************************\

Function: memory_model_baset::add_barriers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void memory_model_baset::add_barriers(
    partial_order_concurrencyt &poc,
    const numbered_evtst &thread,
    const adj_matricest &rf,
    const adj_matricest &ws,
    const adj_matricest &fr,
    adj_matricest &ab)
{
  // e1 -[lw]sync-> e2 --> e1 -ab-> e2
  const std::list<numbered_evtst::const_iterator> barriers=
    thread.barriers_after(**(thread.begin()));
  if(barriers.empty())
    return;

  for(numbered_evtst::const_iterator e_it=thread.begin();
      e_it!=thread.end();
      ++e_it)
  {
    if((*e_it)->direction!=evtt::D_READ &&
        (*e_it)->direction!=evtt::D_WRITE)
      continue;

    for(std::list<numbered_evtst::const_iterator>::const_iterator
        b_it=barriers.begin();
        b_it!=barriers.end();
        ++b_it)
    {
      const bool before_barrier=e_it<*b_it;
      assert(before_barrier || e_it>*b_it);
      const evtt * first_e=before_barrier ? *e_it : **b_it;
      const evtt * second_e=before_barrier ? **b_it : *e_it;
      const exprt guard=(**b_it)->guard.as_expr();

      if((**b_it)->direction==evtt::D_SYNC)
        poc.add_partial_order_constraint(
            AC_GHB, "ab", *first_e, *second_e, guard);
      else
      {
        assert((**b_it)->direction==evtt::D_LWSYNC);

        if((*e_it)->direction==evtt::D_WRITE && !before_barrier)
          poc.add_partial_order_constraint(
              AC_GHB, "ab", *first_e, S_COMMIT, evtt::D_WRITE,
              *second_e, S_COMMIT, evtt::D_WRITE, guard);

        poc.add_partial_order_constraint(
            AC_GHB, "ab", *first_e, S_COMMIT, evtt::D_READ,
            *second_e, S_COMMIT, first_e->direction, guard);
      }

      ab[AC_GHB][first_e].insert(std::make_pair(second_e, guard));
    }
  }
}

#endif
