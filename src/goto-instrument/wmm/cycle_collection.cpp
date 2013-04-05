/*******************************************************************\

Module: collection of cycles in graph of abstract events

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

#include <iostream>

#include "event_graph.h"

//#define DEBUG

#ifdef DEBUG
#define DEBUG_MESSAGE(a) std::cout<<a<<std::endl
#else
#define DEBUG_MESSAGE(a)
#endif

/*******************************************************************\

Function: event_grapht::graph_explorert::filter_thin_air

  Inputs:

 Outputs:

 Purpose: after the collection, eliminates the executions forbidden 
          by an indirect thin-air

\*******************************************************************/
void event_grapht::graph_explorert::filter_thin_air(
  std::set<critical_cyclet>& set_of_cycles)
{
  for(std::set<critical_cyclet>::const_iterator it=set_of_cycles.begin();
    it!=set_of_cycles.end();)
  {
    std::set<critical_cyclet>::const_iterator next=it;
    ++next;
    critical_cyclet::const_iterator e_it=it->begin();
    /* is there an event in the cycle not in thin-air events? */
    for(; e_it!=it->end(); ++e_it)
      if(thin_air_events.find(*e_it)==thin_air_events.end())
        break;

    if(e_it==it->end())
      set_of_cycles.erase(*it);

    it=next;
  }

  for(std::set<unsigned>::const_iterator it=thin_air_events.begin();
    it!=thin_air_events.end();
    ++it)
    std::cout<<egraph[*it]<<";";

  std::cout<<std::endl;
}

/*******************************************************************\

Function: event_grapht::graph_explorert::collect_cycles

  Inputs:

 Outputs:

 Purpose: Tarjan 1972 adapted and modified for events

\*******************************************************************/

void event_grapht::graph_explorert::collect_cycles(
  std::set<critical_cyclet>& set_of_cycles, 
  weak_memory_modelt model)
{
  /* all the events initially unmarked */
  for(unsigned i = 0; i<egraph.size(); i++)
    mark[i] = false;

  std::list<unsigned>* order=0;
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

  for(std::list<unsigned>::const_iterator st_it=order->begin(); 
    st_it!=order->end(); ++st_it)
  {
    unsigned source=*st_it;
    DEBUG_MESSAGE("explore " << egraph[source].id);
    backtrack(set_of_cycles, source, source, 
      false, max_po_trans, false, false, false, "", model);

    while(!marked_stack.empty())
    {
      unsigned up=marked_stack.top();
      mark[up]=false;
      marked_stack.pop();
    }
  }

  /* end of collection -- remove spurious by thin-air cycles */
  filter_thin_air(set_of_cycles);
}

/*******************************************************************\

Function: event_grapht::graph_explorert::extract_cycle

  Inputs:

 Outputs:

 Purpose: extracts a (whole, unreduced) cycle from the stack.
          Note: it may not be a real cycle yet -- we cannot check
          the size before a call to this function.

\*******************************************************************/

event_grapht::critical_cyclet event_grapht::graph_explorert::extract_cycle(
  unsigned vertex, 
  unsigned source,
  unsigned number)
{
  critical_cyclet new_cycle(egraph, number);
  bool incycle=false;
  std::stack<unsigned> stack(point_stack);

  while(!stack.empty())
  {
    unsigned current_vertex=stack.top();
    stack.pop();

    DEBUG_MESSAGE("extract: " << egraph[current_vertex].get_operation() 
      << egraph[current_vertex].variable << "@" 
      << egraph[current_vertex].thread << "~" << egraph[current_vertex].local);

    if(current_vertex==vertex)
      incycle=true;

    if(incycle)
      new_cycle.push_front(current_vertex);

    if(current_vertex==source)
      break;
  }

  return new_cycle;
}

/*******************************************************************\

Function: event_grapht::graph_explorert::backtrack

  Inputs: get_po_only: used for po-transitivity

 Outputs:

 Purpose: see event_grapht::collect_cycles

\*******************************************************************/

bool event_grapht::graph_explorert::backtrack(
  std::set<critical_cyclet> &set_of_cycles, 
  unsigned source, 
  unsigned vertex,
  bool unsafe_met, /* unsafe pair for the model met in the visited path */
  unsigned po_trans, /* po-transition skips still allowed */
  bool same_var_pair, /* in a thread, tells if we already met one rfi wsi fri */
  bool lwfence_met, /* if we try to skip a lwsync (only valid for lwsyncWR) */
  bool has_to_be_unsafe,
  irep_idt var_to_avoid,
  weak_memory_modelt model)
{
#ifdef DEBUG
  for(unsigned i=0; i<80; std::cout << "-", ++i);
  std::cout << std::endl;
  std::cout << "marked size:" << marked_stack.size() << std::endl;
  std::stack<unsigned> tmp;
  while(!point_stack.empty())
  {
    std::cout << point_stack.top() << " | ";
    tmp.push(point_stack.top());
    point_stack.pop();
  }
  std::cout << std::endl;
  while(!tmp.empty())
  { 
    point_stack.push(tmp.top());
    tmp.pop();
  }
  while(!marked_stack.empty())
  {
    std::cout << marked_stack.top() << " | ";
    tmp.push(marked_stack.top());
    marked_stack.pop();
  }
  std::cout << std::endl;
  while(!tmp.empty())
  {
    marked_stack.push(tmp.top());
    tmp.pop();
  }
#endif

  // TO DISCUSS: shouldn't we still allow po-transition through it instead?
  if(filtering(vertex))
    return false;

  DEBUG_MESSAGE("bcktck "<<egraph[vertex].id<<"#"<<vertex<<", "
    <<egraph[source].id<<"#"<<source<<" lw:"<<lwfence_met<<" unsafe:"
    <<unsafe_met);
  bool f=false;
  bool get_com_only=false;
  bool unsafe_met_updated=unsafe_met;
  bool same_var_pair_updated=same_var_pair;

  bool not_thin_air=true;

  const abstract_eventt& this_vertex=egraph[vertex];

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
    if(lwfence_met && this_vertex.operation!=abstract_eventt::Read)
      return false; //{no_comm=true;get_com_only=false;}//return false;

    /* no more than 4 events per thread */
    if(this_vertex.operation!=abstract_eventt::Fence
      && this_vertex.operation!=abstract_eventt::Lwfence
      && this_vertex.operation!=abstract_eventt::ASMfence)
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
      const unsigned previous = point_stack.top();
      point_stack.pop();
      const unsigned preprevious = point_stack.top();
      point_stack.push(previous);
      if(!egraph[preprevious].unsafe_pair(this_vertex,model)
        && !(this_vertex.operation==abstract_eventt::Fence
          || egraph[preprevious].operation==abstract_eventt::Fence
          || this_vertex.operation==abstract_eventt::Lwfence
          || egraph[preprevious].operation==abstract_eventt::Lwfence
          || this_vertex.operation==abstract_eventt::ASMfence
          || egraph[preprevious].operation==abstract_eventt::ASMfence))
        return false;
    }

    bool has_to_be_unsafe_updated = has_to_be_unsafe;

    /* constraint 1.a: there is at most one pair of events per thread
       with different variables. Given that we cannot have more than
       three events on the same variable, with two in the same thread,
       this means that we can have at most 2 consecutive events by po
       with the same variable, and two variables per thread (fences are
       not taken into account) */
    if(!point_stack.empty() && egraph.are_po_ordered(point_stack.top(),vertex)
      && this_vertex.operation!=abstract_eventt::Fence
      && this_vertex.operation!=abstract_eventt::Lwfence
      && this_vertex.operation!=abstract_eventt::ASMfence
      && this_vertex.variable==egraph[point_stack.top()].variable)
    {
      if(same_var_pair || 
        (this_vertex.operation==abstract_eventt::Read 
        && egraph[point_stack.top()].operation==abstract_eventt::Read))
      {
        events_per_thread[this_vertex.thread]--;
        return false; //{no_comm=true;get_com_only=false;} //return false;
      }
      else
      {
        same_var_pair_updated = true;
        if(events_per_thread[this_vertex.thread]>=3)
          get_com_only = true;
      }
    }

    /* constraint 1.b */
    if(!point_stack.empty() && egraph.are_po_ordered(point_stack.top(),vertex)
      && this_vertex.operation!=abstract_eventt::Fence
      && this_vertex.operation!=abstract_eventt::Lwfence
      && this_vertex.operation!=abstract_eventt::ASMfence
      && this_vertex.variable!=egraph[point_stack.top()].variable)
    {
      same_var_pair_updated = false;
    }

    /* constraint 2: per variable, either W W, R W, W R, or R W R */
    if(this_vertex.operation!=abstract_eventt::Fence 
      && this_vertex.operation!=abstract_eventt::Lwfence
      && this_vertex.operation!=abstract_eventt::ASMfence)
    {
      const unsigned char nb_writes = writes_per_variable[this_vertex.variable];
      const unsigned char nb_reads = reads_per_variable[this_vertex.variable];

      if(nb_writes+nb_reads==3)
      {
        events_per_thread[this_vertex.thread]--;
        return false; //{no_comm=true;get_com_only=false;} //return false;
      }
      else if(this_vertex.operation==abstract_eventt::Write)
      {
        if(nb_writes==2)
        {
          events_per_thread[this_vertex.thread]--;
          return false; //{no_comm=true;get_com_only=false;} //return false;
        }
        else
          writes_per_variable[this_vertex.variable]++;
      }
      else if(this_vertex.operation==abstract_eventt::Read)
      {
        if(nb_reads==2)
        {
          events_per_thread[this_vertex.thread]--;
          return false; //{no_comm=true;get_com_only=false;} //return false;
        }
        else
          reads_per_variable[this_vertex.variable]++;
      }
    }

    if(!point_stack.empty())
    {
      const abstract_eventt& prev_vertex = egraph[point_stack.top()];
      unsafe_met_updated |= (prev_vertex.unsafe_pair(this_vertex,model)
        && !(prev_vertex.thread==this_vertex.thread
          && egraph.map_data_dp[this_vertex.thread].dp(prev_vertex,this_vertex)));
      if (unsafe_met_updated && !unsafe_met 
        && egraph.are_po_ordered(point_stack.top(), vertex))
        has_to_be_unsafe_updated=true;
    }

    point_stack.push(vertex);
    mark[vertex]=true;
    marked_stack.push(vertex);

    if(!get_com_only)
    {
      /* we first visit via po transition, if existing */
      for(graph<abstract_eventt>::edgest::const_iterator 
        w_it=egraph.po_out(vertex).begin(); 
        w_it!=egraph.po_out(vertex).end(); w_it++)
      {
        const unsigned w = w_it->first;
        if(w < source)
          egraph.remove_po_edge(vertex,w);
        else if(w == source && point_stack.size()>=4
          && (unsafe_met_updated
            || this_vertex.unsafe_pair(egraph[source],model)) )
        {
          critical_cyclet new_cycle = extract_cycle(vertex, source, cycle_nb++);
          not_thin_air = new_cycle.is_not_thin_air();
          if(!not_thin_air)
          {
            for(critical_cyclet::const_iterator e_it=new_cycle.begin();
              e_it!=new_cycle.end();
              ++e_it)
              thin_air_events.insert(*e_it);
          }
          if(new_cycle.is_not_uniproc(model) && not_thin_air 
            && new_cycle.is_cycle() &&
#ifndef ASMFENCE
            new_cycle.is_unsafe(model))
#else
            new_cycle.is_unsafe_asm(model))
#endif
          {
            DEBUG_MESSAGE(new_cycle.print_name(model,false));
            set_of_cycles.insert(new_cycle);
#if 0
            const critical_cyclet* reduced=new_cycle.hide_internals();
            set_of_cycles.insert(*reduced);
            delete(reduced);
#endif
          }
          f = true;
        }
        else if(!mark[w])
          f |= backtrack(set_of_cycles, source, w, unsafe_met_updated, 
            po_trans, same_var_pair_updated, false, has_to_be_unsafe_updated,
            avoid_at_the_end, model);
      }
    }

    if(!no_comm)
    /* we then visit via com transitions, if existing */
    for(graph<abstract_eventt>::edgest::const_iterator 
      w_it=egraph.com_out(vertex).begin();
      w_it!=egraph.com_out(vertex).end(); w_it++)
    {
      const unsigned w = w_it->first;
      if(w < source)
        egraph.remove_com_edge(vertex,w);
      else if(w == source && point_stack.size()>=4
        && (unsafe_met_updated 
          || this_vertex.unsafe_pair(egraph[source],model)) )
      {
        critical_cyclet new_cycle = extract_cycle(vertex, source, cycle_nb++);
        not_thin_air = new_cycle.is_not_thin_air();
        if(!not_thin_air)
        {
          for(critical_cyclet::const_iterator e_it=new_cycle.begin();
            e_it!=new_cycle.end();
            ++e_it)
            thin_air_events.insert(*e_it);
        }
        if(new_cycle.is_not_uniproc(model) && not_thin_air 
          && new_cycle.is_cycle() &&
#ifndef ASMFENCE
          new_cycle.is_unsafe(model))
#else
          new_cycle.is_unsafe_asm(model))
#endif
        {
          DEBUG_MESSAGE(new_cycle.print_name(model,false));
          set_of_cycles.insert(new_cycle);
#if 0
          const critical_cyclet* reduced=new_cycle.hide_internals();
          set_of_cycles.insert(*reduced);
          delete(reduced);
#endif
        }
        f = true;
      }
      else if(!mark[w])
        f |= backtrack(set_of_cycles, source, w, 
          unsafe_met_updated, po_trans, false, false, false, "", model);
    }

    if(f)
    {
      while(!marked_stack.empty() && marked_stack.top()!=vertex)
      {
        unsigned up = marked_stack.top();
        marked_stack.pop();
        mark[up] = false;
      }

      if(!marked_stack.empty())
        marked_stack.pop();
      mark[vertex] = false;
    }

    assert(!point_stack.empty());
    point_stack.pop();

    /* removes variable access */
    if(this_vertex.operation!=abstract_eventt::Fence 
      && this_vertex.operation!=abstract_eventt::Lwfence
      && this_vertex.operation!=abstract_eventt::ASMfence)
    {
      if(this_vertex.operation==abstract_eventt::Write)
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
  if( skip_tracked.find(vertex)==skip_tracked.end() ) // 25 oct
  if( not_thin_air
    && !get_com_only && (po_trans > 1 || po_trans==0)
    && !point_stack.empty() && egraph.are_po_ordered(point_stack.top(),vertex)
    && this_vertex.operation!=abstract_eventt::Fence
    && ( this_vertex.operation!=abstract_eventt::Lwfence
      || egraph[point_stack.top()].operation==abstract_eventt::Write)
    && ( this_vertex.operation!=abstract_eventt::ASMfence
      || !this_vertex.WRfence 
      || egraph[point_stack.top()].operation==abstract_eventt::Write)
    )
  {
    skip_tracked.insert(vertex);

    std::stack<unsigned> tmp;

    while(marked_stack.size()>0 && marked_stack.top()!=vertex)
    {
      tmp.push(marked_stack.top());
      mark[marked_stack.top()]=false;
      marked_stack.pop();
    }

    if(marked_stack.size()>0)
    {
      assert(marked_stack.top()==vertex);
      mark[vertex]=true;
    }
    else
    {
      while(tmp.size()>0)
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
      avoid_at_the_end = this_vertex.variable;
    }

    /* skip lwfence by po-transition only if we consider a WR */
    // TO CHECK
    const bool is_lwfence = (this_vertex.operation==abstract_eventt::Lwfence
      && egraph[point_stack.top()].operation==abstract_eventt::Write)
      || (this_vertex.operation==abstract_eventt::ASMfence &&
         (!this_vertex.WRfence 
           && egraph[point_stack.top()].operation==abstract_eventt::Write));

    for(graph<abstract_eventt>::edgest::const_iterator w_it=
      egraph.po_out(vertex).begin();
      w_it!=egraph.po_out(vertex).end(); w_it++)
    {
      const unsigned w = w_it->first;
      f |= backtrack(set_of_cycles, source, w,
        unsafe_met/*_updated*/, (po_trans==0?0:po_trans-1), 
        same_var_pair/*_updated*/, is_lwfence, has_to_be_unsafe, avoid_at_the_end,
        model);
    }

    if(f)
    {
      while(!marked_stack.empty() && marked_stack.top()!=vertex)
      {
        unsigned up = marked_stack.top();
        marked_stack.pop();
        mark[up] = false;
      }

      if(!marked_stack.empty())
        marked_stack.pop();
      mark[vertex] = false;
    }

    skip_tracked.erase(vertex);
  }

  return f;
}

