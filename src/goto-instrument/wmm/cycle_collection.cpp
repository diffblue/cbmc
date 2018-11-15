/*******************************************************************\

Module: collection of cycles in graph of abstract events

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

/// \file
/// collection of cycles in graph of abstract events

#include "event_graph.h"

#include <util/message.h>

/// after the collection, eliminates the executions forbidden by an indirect
/// thin-air
void event_grapht::graph_explorert::filter_thin_air(
  std::set<critical_cyclet> &set_of_cycles)
{
  for(std::set<critical_cyclet>::const_iterator it=set_of_cycles.begin();
      it!=set_of_cycles.end(); )
  {
    std::set<critical_cyclet>::const_iterator next=it;
    ++next;
    auto e_it=it->begin();
    /* is there an event in the cycle not in thin-air events? */
    for(; e_it!=it->end(); ++e_it)
      if(thin_air_events.find(*e_it)==thin_air_events.end())
        break;

    if(e_it==it->end())
      set_of_cycles.erase(*it);

    it=next;
  }

#ifdef DEBUG
  for(std::set<event_idt>::const_iterator it=thin_air_events.begin();
      it!=thin_air_events.end();
      ++it)
    egraph.message.debug()<<egraph[*it]<<";";

  egraph.message.debug() << messaget::eom;
#endif
}

/// Tarjan 1972 adapted and modified for events
void event_grapht::graph_explorert::collect_cycles(
  std::set<critical_cyclet> &set_of_cycles,
  memory_modelt model)
{
  /* all the events initially unmarked */
  for(std::size_t i=0; i<egraph.size(); i++)
    mark[i]=false;

  std::list<event_idt>* order=nullptr;
  /* on Power, rfe pairs are also potentially unsafe */
  switch(model)
  {
  case TSO:
  case PSO:
  case RMO:
    order=&egraph.po_order;
    break;
  case Power:
    order=&egraph.poUrfe_order;
    break;

  case Unknown:
    assert(false);
  }

  if(order->empty())
    return;

  /* if we only consider a limited part of the graph */
  order=order_filtering(order);

  if(order->empty())
    return;

  for(std::list<event_idt>::const_iterator
      st_it=order->begin();
      st_it!=order->end();
      ++st_it)
  {
    event_idt source=*st_it;
    egraph.message.debug() << "explore " << egraph[source].id << messaget::eom;
    backtrack(set_of_cycles, source, source,
      false, max_po_trans, false, false, false, "", model);

    while(!marked_stack.empty())
    {
      event_idt up=marked_stack.top();
      mark[up]=false;
      marked_stack.pop();
    }
  }

  /* end of collection -- remove spurious by thin-air cycles */
  if(egraph.filter_thin_air)
    filter_thin_air(set_of_cycles);
}

/// extracts a (whole, unreduced) cycle from the stack. Note: it may not be a
/// real cycle yet -- we cannot check the size before a call to this function.
event_grapht::critical_cyclet event_grapht::graph_explorert::extract_cycle(
  event_idt vertex,
  event_idt source,
  unsigned number)
{
  critical_cyclet new_cycle(egraph, number);
  bool incycle=false;
  std::stack<event_idt> stack(point_stack);

  while(!stack.empty())
  {
    event_idt current_vertex=stack.top();
    stack.pop();

    egraph.message.debug() << "extract: "
                           << egraph[current_vertex].get_operation()
                           << egraph[current_vertex].variable << "@"
                           << egraph[current_vertex].thread << "~"
                           << egraph[current_vertex].local
                           << messaget::eom;

    if(!new_cycle.has_user_defined_fence)
    {
      new_cycle.has_user_defined_fence=egraph[current_vertex].is_fence();
    }

    if(current_vertex==vertex)
      incycle=true;

    if(incycle)
      new_cycle.push_front(current_vertex);

    if(current_vertex==source)
      break;
  }

  return new_cycle;
}

/// see event_grapht::collect_cycles
bool event_grapht::graph_explorert::backtrack(
  std::set<critical_cyclet> &set_of_cycles,
  event_idt source,
  event_idt vertex,
  bool unsafe_met, /* unsafe pair for the model met in the visited path */
  event_idt po_trans, /* po-transition skips still allowed */
  bool same_var_pair, /* in a thread, tells if we already met one rfi wsi fri */
  bool lwfence_met, /* if we try to skip a lwsync (only valid for lwsyncWR) */
  bool has_to_be_unsafe,
  irep_idt var_to_avoid,
  memory_modelt model)
{
#ifdef DEBUG
  egraph.message.debug() << std::string(80, '-');
  egraph.message.debug() << messaget::eom;
  egraph.message.debug() << "marked size:" << marked_stack.size()
    << messaget::eom;
  std::stack<event_idt> tmp;
  while(!point_stack.empty())
  {
    egraph.message.debug() << point_stack.top() << " | ";
    tmp.push(point_stack.top());
    point_stack.pop();
  }
  egraph.message.debug() << messaget::eom;
  while(!tmp.empty())
  {
    point_stack.push(tmp.top());
    tmp.pop();
  }
  while(!marked_stack.empty())
  {
    egraph.message.debug() << marked_stack.top() << " | ";
    tmp.push(marked_stack.top());
    marked_stack.pop();
  }
  egraph.message.debug() << messaget::eom;
  while(!tmp.empty())
  {
    marked_stack.push(tmp.top());
    tmp.pop();
  }
#endif

  // TO DISCUSS: shouldn't we still allow po-transition through it instead?
  if(filtering(vertex))
    return false;

  egraph.message.debug() << "bcktck "<<egraph[vertex].id<<"#"<<vertex<<", "
    <<egraph[source].id<<"#"<<source<<" lw:"<<lwfence_met<<" unsafe:"
    <<unsafe_met << messaget::eom;
  bool f=false;
  bool get_com_only=false;
  bool unsafe_met_updated=unsafe_met;
  bool same_var_pair_updated=same_var_pair;

  bool not_thin_air=true;

  const abstract_eventt &this_vertex=egraph[vertex];

  /* if a thread starts with variable x, the last event of this thread in the
     cycle cannot be with x */
  irep_idt avoid_at_the_end=var_to_avoid;
  bool no_comm=false;
  if(avoid_at_the_end!="" && avoid_at_the_end==this_vertex.variable)
    no_comm=true;

  /* if specified, maximum number of events reached */
  if(max_var!=0 && point_stack.size()>max_var*3)
    return false;

  /* we only explore shared variables */
  if(!this_vertex.local)
  {
    /* only the lwsyncWR can be interpreted as poWR (i.e., skip of the fence) */
    if(lwfence_met && this_vertex.operation!=abstract_eventt::operationt::Read)
      return false; // {no_comm=true;get_com_only=false;}//return false;

    bool has_to_be_unsafe_updated=false;
    // TODO: propagate this constraint within the optimisation
    // -- no optimisation can strongly affect performances
    /* tab[] can appear several times */
    if(egraph.ignore_arrays ||
       id2string(this_vertex.variable).find("[]")==std::string::npos)
    {
      /* no more than 4 events per thread */
      if(this_vertex.operation!=abstract_eventt::operationt::Fence &&
         this_vertex.operation!=abstract_eventt::operationt::Lwfence &&
         this_vertex.operation!=abstract_eventt::operationt::ASMfence)
      {
        if(events_per_thread[this_vertex.thread]==4)
          return false;
        else
          events_per_thread[this_vertex.thread]++;
      }

      /* Multiple re-orderings constraint: if the thread on this cycles contains
         more than one, ensure that an unsafe pair is not protected by another
         relation in the thread. E.g., in Wx Rx Wy, under TSO, the rfi cannot be
         delayed, since the only way to make this transformation matter is to
         re-order also the two writes, which is not permitted on TSO. */
      if(has_to_be_unsafe && point_stack.size() >= 2)
      {
        const event_idt previous=point_stack.top();
        point_stack.pop();
        const event_idt preprevious=point_stack.top();
        point_stack.push(previous);
        if(!egraph[preprevious].unsafe_pair(this_vertex, model) &&
           !(this_vertex.operation==abstract_eventt::operationt::Fence ||
             egraph[preprevious].operation==
               abstract_eventt::operationt::Fence ||
             this_vertex.operation==abstract_eventt::operationt::Lwfence ||
             egraph[preprevious].operation==
               abstract_eventt::operationt::Lwfence ||
             this_vertex.operation==abstract_eventt::operationt::ASMfence ||
             egraph[preprevious].operation==
               abstract_eventt::operationt::ASMfence))
          return false;
      }
    }

    has_to_be_unsafe_updated=has_to_be_unsafe;

    /* constraint 1.a: there is at most one pair of events per thread
       with different variables. Given that we cannot have more than
       three events on the same variable, with two in the same thread,
       this means that we can have at most 2 consecutive events by po
       with the same variable, and two variables per thread (fences are
       not taken into account) */
    if(!point_stack.empty() &&
       egraph.are_po_ordered(point_stack.top(), vertex) &&
       this_vertex.operation!=abstract_eventt::operationt::Fence &&
       this_vertex.operation!=abstract_eventt::operationt::Lwfence &&
       this_vertex.operation!=abstract_eventt::operationt::ASMfence &&
       this_vertex.variable==egraph[point_stack.top()].variable)
    {
      if(same_var_pair ||
         (this_vertex.operation==abstract_eventt::operationt::Read &&
          egraph[point_stack.top()].operation==
            abstract_eventt::operationt::Read))
      {
        events_per_thread[this_vertex.thread]--;
        return false; // {no_comm=true;get_com_only=false;} //return false;
      }
      else
      {
        same_var_pair_updated=true;
        if(events_per_thread[this_vertex.thread]>=3)
          get_com_only=true;
      }
    }

    /* constraint 1.b */
    if(!point_stack.empty() &&
       egraph.are_po_ordered(point_stack.top(), vertex) &&
       this_vertex.operation!=abstract_eventt::operationt::Fence &&
       this_vertex.operation!=abstract_eventt::operationt::Lwfence &&
       this_vertex.operation!=abstract_eventt::operationt::ASMfence &&
       this_vertex.variable!=egraph[point_stack.top()].variable)
    {
      same_var_pair_updated=false;
    }

    /* constraint 2: per variable, either W W, R W, W R, or R W R */
    if(this_vertex.operation!=abstract_eventt::operationt::Fence &&
       this_vertex.operation!=abstract_eventt::operationt::Lwfence &&
       this_vertex.operation!=abstract_eventt::operationt::ASMfence)
    {
      const unsigned char nb_writes=writes_per_variable[this_vertex.variable];
      const unsigned char nb_reads=reads_per_variable[this_vertex.variable];

      if(nb_writes+nb_reads==3)
      {
        events_per_thread[this_vertex.thread]--;
        return false; // {no_comm=true;get_com_only=false;} //return false;
      }
      else if(this_vertex.operation==abstract_eventt::operationt::Write)
      {
        if(nb_writes==2)
        {
          events_per_thread[this_vertex.thread]--;
          return false; // {no_comm=true;get_com_only=false;} //return false;
        }
        else
          writes_per_variable[this_vertex.variable]++;
      }
      else if(this_vertex.operation==abstract_eventt::operationt::Read)
      {
        if(nb_reads==2)
        {
          events_per_thread[this_vertex.thread]--;
          return false; // {no_comm=true;get_com_only=false;} //return false;
        }
        else
          reads_per_variable[this_vertex.variable]++;
      }
    }

    if(!point_stack.empty())
    {
      const abstract_eventt &prev_vertex=egraph[point_stack.top()];
      unsafe_met_updated|=
        prev_vertex.unsafe_pair(this_vertex, model) &&
        !(prev_vertex.thread==this_vertex.thread &&
          egraph.map_data_dp[this_vertex.thread].dp(prev_vertex, this_vertex));
      if(unsafe_met_updated &&
         !unsafe_met &&
         egraph.are_po_ordered(point_stack.top(), vertex))
        has_to_be_unsafe_updated=true;
    }

    point_stack.push(vertex);
    mark[vertex]=true;
    marked_stack.push(vertex);

    if(!get_com_only)
    {
      /* we first visit via po transition, if existing */
      for(wmm_grapht::edgest::const_iterator
        w_it=egraph.po_out(vertex).begin();
        w_it!=egraph.po_out(vertex).end(); w_it++)
      {
        const event_idt w=w_it->first;
        if(w==source && point_stack.size()>=4
          && (unsafe_met_updated
            || this_vertex.unsafe_pair(egraph[source], model)) )
        {
          critical_cyclet new_cycle=extract_cycle(vertex, source, cycle_nb++);
          not_thin_air=!egraph.filter_thin_air || new_cycle.is_not_thin_air();
          if(!not_thin_air)
          {
            for(critical_cyclet::const_iterator e_it=new_cycle.begin();
              e_it!=new_cycle.end();
              ++e_it)
              thin_air_events.insert(*e_it);
          }
          if((!egraph.filter_uniproc || new_cycle.is_not_uniproc(model)) &&
             not_thin_air && new_cycle.is_cycle() &&
             new_cycle.is_unsafe(model) /*&& new_cycle.is_unsafe_asm(model)*/)
          {
            egraph.message.debug() << new_cycle.print_name(model, false)
              << messaget::eom;
            set_of_cycles.insert(new_cycle);
#if 0
            const critical_cyclet* reduced=new_cycle.hide_internals();
            set_of_cycles.insert(*reduced);
            delete(reduced);
#endif
          }
          f=true;
        }
        else if(!mark[w])
          f|=
            backtrack(
              set_of_cycles,
              source,
              w,
              unsafe_met_updated,
              po_trans,
              same_var_pair_updated,
              false,
              has_to_be_unsafe_updated,
              avoid_at_the_end, model);
      }
    }

    if(!no_comm)
    {
      /* we then visit via com transitions, if existing */
      for(wmm_grapht::edgest::const_iterator
          w_it=egraph.com_out(vertex).begin();
          w_it!=egraph.com_out(vertex).end(); w_it++)
      {
        const event_idt w=w_it->first;
        if(w < source)
          egraph.remove_com_edge(vertex, w);
        else if(w==source && point_stack.size()>=4 &&
                (unsafe_met_updated ||
                 this_vertex.unsafe_pair(egraph[source], model)))
        {
          critical_cyclet new_cycle=extract_cycle(vertex, source, cycle_nb++);
          not_thin_air=!egraph.filter_thin_air || new_cycle.is_not_thin_air();
          if(!not_thin_air)
          {
            for(critical_cyclet::const_iterator e_it=new_cycle.begin();
                e_it!=new_cycle.end();
                ++e_it)
              thin_air_events.insert(*e_it);
          }
          if((!egraph.filter_uniproc || new_cycle.is_not_uniproc(model)) &&
             not_thin_air && new_cycle.is_cycle() &&
             new_cycle.is_unsafe(model) /*&& new_cycle.is_unsafe_asm(model)*/)
          {
            egraph.message.debug() << new_cycle.print_name(model, false)
              << messaget::eom;
            set_of_cycles.insert(new_cycle);
#if 0
            const critical_cyclet* reduced=new_cycle.hide_internals();
            set_of_cycles.insert(*reduced);
            delete(reduced);
#endif
          }
          f=true;
        }
        else if(!mark[w])
          f|=
            backtrack(
              set_of_cycles,
              source,
              w,
              unsafe_met_updated,
              po_trans,
              false,
              false,
              false,
              "",
              model);
      }
    }

    if(f)
    {
      while(!marked_stack.empty() && marked_stack.top()!=vertex)
      {
        event_idt up=marked_stack.top();
        marked_stack.pop();
        mark[up]=false;
      }

      if(!marked_stack.empty())
        marked_stack.pop();
      mark[vertex]=false;
    }

    assert(!point_stack.empty());
    point_stack.pop();

    /* removes variable access */
    if(this_vertex.operation!=abstract_eventt::operationt::Fence &&
       this_vertex.operation!=abstract_eventt::operationt::Lwfence &&
       this_vertex.operation!=abstract_eventt::operationt::ASMfence)
    {
      if(this_vertex.operation==abstract_eventt::operationt::Write)
        writes_per_variable[this_vertex.variable]--;
      else
        reads_per_variable[this_vertex.variable]--;

      events_per_thread[this_vertex.thread]--;
    }
  }

  /* transitivity of po: do the same, but skip this event
     (except if it is a fence or no more po-transition skips allowed);
     if the cycle explored so far has a thin-air subcycle, this cycle
     is not valid: stop this exploration here */
  if(skip_tracked.find(vertex)==skip_tracked.end()) // 25 oct
    if(not_thin_air && !get_com_only &&
       (po_trans > 1 || po_trans==0) &&
       !point_stack.empty() &&
       egraph.are_po_ordered(point_stack.top(), vertex) &&
       this_vertex.operation!=abstract_eventt::operationt::Fence &&
       (this_vertex.operation!=abstract_eventt::operationt::Lwfence ||
        egraph[point_stack.top()].operation==
          abstract_eventt::operationt::Write) &&
       (this_vertex.operation!=abstract_eventt::operationt::ASMfence ||
        !this_vertex.WRfence ||
        egraph[point_stack.top()].operation==
          abstract_eventt::operationt::Write))
    {
      skip_tracked.insert(vertex);

      std::stack<event_idt> tmp;

      while(!marked_stack.empty() && marked_stack.top()!=vertex)
      {
        tmp.push(marked_stack.top());
        mark[marked_stack.top()]=false;
        marked_stack.pop();
      }

      if(!marked_stack.empty())
      {
        assert(marked_stack.top()==vertex);
        mark[vertex]=true;
      }
      else
      {
        while(!tmp.empty())
        {
          marked_stack.push(tmp.top());
          mark[tmp.top()]=true;
          tmp.pop();
        }
        mark[vertex]=true;
        marked_stack.push(vertex);
      }

      if(!egraph[point_stack.top()].unsafe_pair(this_vertex, model))
      {
        /* tab[] should never be avoided */
        if(egraph.ignore_arrays ||
           id2string(this_vertex.variable).find("[]")==std::string::npos)
          avoid_at_the_end=this_vertex.variable;
      }

      /* skip lwfence by po-transition only if we consider a WR */
      // TO CHECK
      const bool is_lwfence=
        (this_vertex.operation==abstract_eventt::operationt::Lwfence &&
         egraph[point_stack.top()].operation==
           abstract_eventt::operationt::Write) ||
        (this_vertex.operation==abstract_eventt::operationt::ASMfence &&
         (!this_vertex.WRfence &&
          egraph[point_stack.top()].operation==
            abstract_eventt::operationt::Write));

      for(wmm_grapht::edgest::const_iterator w_it=
          egraph.po_out(vertex).begin();
          w_it!=egraph.po_out(vertex).end(); w_it++)
      {
        const event_idt w=w_it->first;
        f|=
          backtrack(
            set_of_cycles,
            source,
            w,
            unsafe_met/*_updated*/,
            (po_trans==0?0:po_trans-1),
            same_var_pair/*_updated*/,
            is_lwfence,
            has_to_be_unsafe,
            avoid_at_the_end,
            model);
      }

      if(f)
      {
        while(!marked_stack.empty() && marked_stack.top()!=vertex)
        {
          event_idt up=marked_stack.top();
          marked_stack.pop();
          mark[up]=false;
        }

        if(!marked_stack.empty())
          marked_stack.pop();
        mark[vertex]=false;
      }

      skip_tracked.erase(vertex);
    }

  return f;
}
