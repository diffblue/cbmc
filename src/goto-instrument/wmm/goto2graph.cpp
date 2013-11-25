/*******************************************************************\

Module: Turns a goto-program into an abstract event graph

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

#include <vector>
#include <string>
#include <fstream>
#include <iostream>

#ifndef _WIN32
#include <cstdlib>
#endif

#include <util/prefix.h>
#include <util/cprover_prefix.h>
#include <util/options.h>
#include <util/message.h>
#include <util/i2string.h>

#include "../rw_set.h"
#include "fence.h"
#include "goto2graph.h"

//#define DEBUG
//#define PRINT_UNSAFES

#ifdef DEBUG
#define DEBUG_MESSAGE(a) std::cout<<a<<std::endl
#else
#define DEBUG_MESSAGE(a)
#endif

/*******************************************************************\

Function: instrumentert::local

  Inputs:
 
 Outputs:
 
 Purpose: is local variable?

\*******************************************************************/

bool inline instrumentert::local(const irep_idt& id)
{
  std::string identifier = id2string(id);

  if(has_prefix(identifier, "symex_invalid") || has_prefix(identifier, "symex::invalid"))
  {
    /* symex_invalid and symex::invalid_object generated when pointer analysis
       fails */
    return true;
  }

  if(identifier=="c::__CPROVER_alloc" ||
    identifier=="c::__CPROVER_alloc_size" ||
    identifier=="c::stdin" ||
    identifier=="c::stdout" ||
    identifier=="c::stderr" ||
    identifier=="c::sys_nerr" ||
    has_prefix(identifier, "__unbuffered_") ||
    has_prefix(identifier, "c::__unbuffered_") )
    return true;
 
  const size_t pos = identifier.find("[]");

  if(pos!=std::string::npos)
  {
    /* we don't distinguish the members of an array for the moment */
    identifier.erase(pos);
  }

  try
  {
    const symbolt& symbol = ns.lookup(identifier);

    if(!symbol.is_static_lifetime)
      return true; /* these are local */

    if(symbol.is_thread_local)
      return true; /* these are local */

    return false;
  }
  catch(std::string exception)
  {
    DEBUG_MESSAGE("Exception: "<<exception);
    return false;
  }
}

/*******************************************************************\

Function: instrumentert::extract_events_rw
  
  Inputs:
  
 Outputs:
  
 Purpose: 
  
\*******************************************************************/

void instrumentert::extract_events_rw(
  value_setst& value_sets,
  memory_modelt model,
  bool no_dependencies,
  goto_programt::const_targett target,
  thread_eventst &dest)
{
  const goto_programt::instructiont &instruction=*target;

  rw_set_loct rw_set(ns, value_sets, target);

  /* Read (Rb) */
  forall_rw_set_r_entries(r_it, rw_set)
  {
    /* creates Read:
       read is the irep_id of the read in the code;
       new_read_event is the corresponding abstract event;
       new_read_node is the node in the graph */
    const irep_idt& read=r_it->second.object;

    /* skip local variables */
    if(local(read))
      continue;

    read_counter++;

    const abstract_eventt new_read_event(abstract_eventt::Read,
      thread, read, unique_id++,
      instruction.location, local(read));
    const unsigned new_read_node=egraph.add_node();
    egraph[new_read_node]=new_read_event;
    DEBUG_MESSAGE("new Read"<<read<<" @thread"
      <<(thread)<<"("<<instruction.location<<","
      <<(local(read)?"local":"shared")<<") #"<<new_read_node);

    const unsigned new_read_gnode=egraph_alt.add_node();
    egraph_alt[new_read_gnode]=new_read_event;
    map_vertex_gnode.insert(
      std::make_pair(new_read_node,new_read_gnode));

    map_reads.insert(id2node_pairt(read,new_read_node));

    dest.reads.push_back(new_read_node);
  }

  /* Write (Wa) */
  forall_rw_set_w_entries(w_it, rw_set)
  {
    /* creates Write:
       write is the irep_id in the code;
       new_write_event is the corresponding abstract event;
       new_write_node is the node in the graph */
    const irep_idt& write = w_it->second.object;
    /* skip local variables */
    if(local(write))
      continue;

    ++write_counter;

    /* creates Write */
    const abstract_eventt new_write_event(abstract_eventt::Write,
      thread, write, unique_id++,
      instruction.location, local(write));
    const unsigned new_write_node=egraph.add_node();
    egraph[new_write_node](new_write_event);
    DEBUG_MESSAGE("new Write "<<write<<" @thread"<<(thread)
      <<"("<<instruction.location<<","
      << (local(write)?"local":"shared")<<") #"<<new_write_node);

    const unsigned new_write_gnode=egraph_alt.add_node();
    egraph_alt[new_write_gnode]=new_write_event;
    map_vertex_gnode.insert(
      std::pair<unsigned,unsigned>(new_write_node, new_write_gnode));

    map_writes.insert(id2node_pairt(write,new_write_node));

    dest.writes.push_back(new_write_node);
  }

  /* data dependency analysis */
  if(target->is_assign() &&
     !no_dependencies)
  {
    forall_rw_set_w_entries(write_it, rw_set)
      forall_rw_set_r_entries(read_it, rw_set)
      {
        const irep_idt& write=write_it->second.object;
        const irep_idt& read=read_it->second.object;
        DEBUG_MESSAGE("dp: Write:"<<write<<"; Read:"<<read);
        const datat read_p(read,instruction.location);
        const datat write_p(write,instruction.location);
          data_dp.dp_analysis(read_p,local(read),write_p,local(write));
        }
    data_dp.dp_merge();

    forall_rw_set_r_entries(read2_it, rw_set)
      forall_rw_set_r_entries(read_it, rw_set)
      {
        const irep_idt& read2=read2_it->second.object;
        const irep_idt& read=read_it->second.object;
        if(read2==read)
          continue;
        const datat read_p(read,instruction.location);
        const datat read2_p(read2,instruction.location);
        data_dp.dp_analysis(read_p,local(read),read2_p,local(read2));
      }
    data_dp.dp_merge();
  }
}

/*******************************************************************\

Function: instrumentert::extract_events_fence
  
  Inputs:
  
 Outputs:
  
 Purpose: 
  
\*******************************************************************/

void instrumentert::extract_events_fence(
  memory_modelt model,
  goto_programt::const_targett target,
  thread_eventst &dest)
{
  const goto_programt::instructiont& instruction=*target;

  if(is_fence(instruction, ns))
  {
    const abstract_eventt new_fence_event(abstract_eventt::Fence,
      thread, "F", unique_id++, instruction.location, false);
    const unsigned new_fence_node=egraph.add_node();
    egraph[new_fence_node](new_fence_event);
    const unsigned new_fence_gnode=egraph_alt.add_node();
    egraph_alt[new_fence_gnode]=new_fence_event;
    map_vertex_gnode.insert(
      std::make_pair(new_fence_node, new_fence_gnode));

    dest.fences.push_back(new_fence_node);
  }
  else if(is_lwfence(instruction, ns))
  {
    if(model!=TSO)
    {
      const abstract_eventt new_fence_event(abstract_eventt::Lwfence,
        thread, "f", unique_id++, instruction.location, false);
      const unsigned new_fence_node=egraph.add_node();
      egraph[new_fence_node](new_fence_event);
      const unsigned new_fence_gnode=egraph_alt.add_node();
      egraph_alt[new_fence_gnode]=new_fence_event;
      map_vertex_gnode.insert(
        std::make_pair(new_fence_node, new_fence_gnode));

      dest.fences.push_back(new_fence_node);
    }
  }
  else if(instruction.is_other() &&
          instruction.code.get_statement()==ID_fence)
  {
    bool WRfence=instruction.code.get_bool(ID_WRfence);
    bool WWfence=instruction.code.get_bool(ID_WWfence);
    bool RRfence=instruction.code.get_bool(ID_RRfence);
    bool RWfence=instruction.code.get_bool(ID_RWfence);
    bool WWcumul=instruction.code.get_bool(ID_WWcumul);
    bool RRcumul=instruction.code.get_bool(ID_RRcumul);
    bool RWcumul=instruction.code.get_bool(ID_RWcumul);
    const abstract_eventt new_fence_event(abstract_eventt::ASMfence,
      thread, "asm", unique_id++, instruction.location,
      false, WRfence, WWfence, RRfence, RWfence, WWcumul, RWcumul, RRcumul);
    const unsigned new_fence_node=egraph.add_node();
    egraph[new_fence_node](new_fence_event);
    const unsigned new_fence_gnode=egraph_alt.add_node();
    egraph_alt[new_fence_gnode]=new_fence_event;
    map_vertex_gnode.insert(
      std::make_pair(new_fence_node, new_fence_gnode));

    dest.fences.push_back(new_fence_node);
  }
}

/*******************************************************************\

Function: instrumentert::extract_events
  
  Inputs:
  
 Outputs:
  
 Purpose: 
  
\*******************************************************************/

void instrumentert::extract_events(
  value_setst& value_sets,
  memory_modelt model,
  bool no_dependencies,
  cfgt::entryt &cfg_entry)
{
  goto_programt::const_targett target=cfg_entry.PC;
  thread_eventst &dest=cfg_entry.events[thread];

  extract_events_rw(value_sets, model, no_dependencies, target, dest);
  extract_events_fence(model, target, dest);
}

/*******************************************************************\

Function: instrumentert::forward_traverse_once
  
  Inputs:
  
 Outputs:
  
 Purpose: 
  
\*******************************************************************/

void instrumentert::forward_traverse_once(
    value_setst& value_sets,
    memory_modelt model,
    bool no_dependencies,
    goto_programt::const_targett target)
{
  cfgt::entryt &cfg_entry=cfg.entry_map[target];

  // we extract events only once per thread; this also means that
  // we do not track call stacks
  if(cfg_entry.events.find(thread)==cfg_entry.events.end())
    extract_events(
      value_sets,
      model,
      no_dependencies,
      cfg_entry);

  goto_programt::const_targett next_PC=target;
  ++next_PC;

  const goto_programt::instructiont& instruction=*cfg_entry.PC;

  if(instruction.is_start_thread())
  {
    /* thread marking */
    unsigned coming_from=thread;

    // explore the spawned thread
    thread=++max_thread;
    assert(instruction.targets.size()==1);
    forward_traverse_once(
      value_sets,
      model,
      no_dependencies,
      instruction.targets.front());

    thread=coming_from;

    assert(cfg_entry.successors.size()==1 &&
           cfg_entry.successors.front()->PC==next_PC);
  }
  else if(instruction.is_end_thread())
  {
    assert(cfg_entry.successors.empty());
  }
  else if(instruction.is_function_call())
  {
    const exprt& fun=to_code_function_call(instruction.code).function();
    const irep_idt& fun_id=to_symbol_expr(fun).get_identifier();

    // do not enter recursion and skip __CPROVER_initialize
    assert(cfg_entry.successors.size()==1);
    if(cfg_entry.successors.front()->PC!=next_PC)
    {
      if(fun_id!=CPROVER_PREFIX "initialize" &&
         functions_met.insert(fun_id).second)
        forward_traverse_once(
          value_sets,
          model,
          no_dependencies,
          cfg_entry.successors.front()->PC);

      forward_traverse_once(
        value_sets,
        model,
        no_dependencies,
        next_PC);

      return;
    }
  }
  else if(instruction.is_end_function())
  {
    functions_met.erase(instruction.function);

    // update dependencies at end of each function
    egraph.map_data_dp[thread]=data_dp;
    // data_dp.print();

    return;
  }
  else if(instruction.is_goto())
  {
    for(cfgt::entriest::const_iterator
        it=cfg_entry.successors.begin();
        it!=cfg_entry.successors.end();
        ++it)
    {
      const cfgt::entryt &succ_entry=cfg.entry_map[(*it)->PC];
      if(succ_entry.events.find(thread)==succ_entry.events.end())
        forward_traverse_once(
          value_sets,
          model,
          no_dependencies,
          succ_entry.PC);
    }

    return;
  }

  if(cfg_entry.successors.empty())
  {
    /* forward traversal done for this thread or branch */
    return;
  }

  assert(cfg_entry.successors.size()==1);

  forward_traverse_once(
    value_sets,
    model,
    no_dependencies,
    cfg_entry.successors.front()->PC);
}

/*******************************************************************\

Function: instrumentert::forward_traverse_once
  
  Inputs:
  
 Outputs:
  
 Purpose: 
  
\*******************************************************************/

void instrumentert::forward_traverse_once(
    value_setst& value_sets,
    memory_modelt model,
    bool no_dependencies)
{
  const goto_programt &goto_program=
    goto_functions.function_map[goto_functions.entry_point()].body;

  if(!goto_program.instructions.empty())
    forward_traverse_once(
      value_sets,
      model,
      no_dependencies,
      goto_program.instructions.begin());
}

/*******************************************************************\

Function: instrumentert::propagate_events_in_po
  
  Inputs:
  
 Outputs:
  
 Purpose: 
  
\*******************************************************************/

void instrumentert::propagate_events_in_po()
{
  std::list<goto_programt::const_targett> worklist;

  // initialise worklist to all instructions seen in forward traversal
  for(cfgt::entry_mapt::const_iterator it=cfg.entry_map.begin();
      it!=cfg.entry_map.end();
      ++it)
    if(!it->second.events.empty())
      worklist.push_back(it->first);

  while(!worklist.empty())
  {
    goto_programt::const_targett target=worklist.back();
    worklist.pop_back();

    cfgt::entryt &cfg_entry=cfg.entry_map[target];

    // consistency checks first
    if(!cfg_entry.events.empty())
    {
      for(std::map<unsigned, thread_eventst>::const_iterator
          it1=cfg_entry.events.begin(), it2=++(cfg_entry.events.begin());
          it1!=cfg_entry.events.end() && it2!=cfg_entry.events.end();
          ++it1, ++it2)
        assert(it1->second.reads.size()==it2->second.reads.size() &&
               it1->second.writes.size()==it2->second.writes.size() &&
               it1->second.fences.size()==it2->second.fences.size());
    }

    const std::set<goto_programt::const_targett>::size_type size_before=
      cfg_entry.use_events_from.size();

    if(!cfg_entry.events.empty() &&
       (!cfg_entry.events.begin()->second.reads.empty() ||
        !cfg_entry.events.begin()->second.writes.empty() ||
        !cfg_entry.events.begin()->second.fences.empty()))
      cfg_entry.use_events_from.insert(target);
    else
    {
      // no events at this instruction -- take the union of all events
      // propagated to predecessors
      for(cfgt::entriest::const_iterator
          it=cfg_entry.predecessors.begin();
          it!=cfg_entry.predecessors.end();
          ++it)
      {
        const std::set<goto_programt::const_targett> &s=
          cfg.entry_map[(*it)->PC].use_events_from;
        cfg_entry.use_events_from.insert(s.begin(), s.end());
      }
    }

    if(cfg_entry.use_events_from.size()>size_before)
      for(cfgt::entriest::const_iterator
          it=cfg_entry.successors.begin();
          it!=cfg_entry.successors.end();
          ++it)
        worklist.push_front((*it)->PC);
  }
}

/*******************************************************************\

Function: instrumentert::add_po_edges
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void instrumentert::add_po_edges(
  const nodest &from_events,
  const unsigned event_node,
  const unsigned event_gnode,
  const bool is_backward)
{
  for(nodest::const_iterator
      it=from_events.begin();
      it!=from_events.end();
      ++it)
  {
    const unsigned from_node=*it;
    assert(map_vertex_gnode.find(from_node)!=map_vertex_gnode.end());
    const unsigned from_gnode=map_vertex_gnode[from_node];

    DEBUG_MESSAGE(from_node<<"-po->"<<event_node);

    if(is_backward)
      egraph.add_po_back_edge(from_node, event_node);
    else
      egraph.add_po_edge(from_node, event_node);

    egraph_alt.add_edge(from_gnode, event_gnode);
  }
}

/*******************************************************************\

Function: instrumentert::add_po_edges
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void instrumentert::add_po_edges(
  const unsigned thread_nr,
  const cfgt::entryt &from,
  const cfgt::entryt &to,
  const unsigned event_node,
  const unsigned event_gnode)
{
  const bool backward=
    from.PC->function==to.PC->function &&
    from.PC->location_number>to.PC->location_number;

  std::map<unsigned, thread_eventst>::const_iterator thread_entry=
    from.events.find(thread_nr);
  if(thread_entry==from.events.end())
    return;

  const thread_eventst &from_events=thread_entry->second;

  if(!from_events.fences.empty())
    add_po_edges(from_events.fences, event_node, event_gnode, backward);
  else if(!from_events.writes.empty())
    add_po_edges(from_events.writes, event_node, event_gnode, backward);
  else if(!from_events.reads.empty())
    add_po_edges(from_events.reads, event_node, event_gnode, backward);
  else
    assert(false);
}

/*******************************************************************\

Function: instrumentert::add_po_edges
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void instrumentert::add_po_edges(
  const cfgt::entryt &cfg_entry,
  const unsigned thread_nr,
  const unsigned event_node)
{
  assert(map_vertex_gnode.find(event_node)!=map_vertex_gnode.end());
  const unsigned event_gnode=map_vertex_gnode[event_node];

  for(cfgt::entriest::const_iterator
      it=cfg_entry.predecessors.begin();
      it!=cfg_entry.predecessors.end();
      ++it)
  {
    const std::set<goto_programt::const_targett> &s=
      cfg.entry_map[(*it)->PC].use_events_from;

    for(std::set<goto_programt::const_targett>::const_iterator
        s_it=s.begin();
        s_it!=s.end();
        ++s_it)
      // no self-loops
      if(*s_it!=cfg_entry.PC)
        add_po_edges(
          thread_nr,
          cfg.entry_map[*s_it],
          cfg_entry,
          event_node,
          event_gnode);
  }
}

/*******************************************************************\

Function: instrumentert::add_po_edges
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void instrumentert::add_po_edges(
  const cfgt::entryt &cfg_entry,
  const unsigned thread_nr,
  const thread_eventst &thread_events)
{
  for(nodest::const_iterator
      it=thread_events.reads.begin();
      it!=thread_events.reads.end();
      ++it)
    add_po_edges(cfg_entry, thread_nr, *it);

  if(thread_events.reads.empty())
    for(nodest::const_iterator
        it=thread_events.writes.begin();
        it!=thread_events.writes.end();
        ++it)
      add_po_edges(cfg_entry, thread_nr, *it);

  assert(thread_events.fences.empty() ||
         (thread_events.reads.empty() && thread_events.writes.empty()));
  for(nodest::const_iterator
      it=thread_events.fences.begin();
      it!=thread_events.fences.end();
      ++it)
    add_po_edges(cfg_entry, thread_nr, *it);
}

/*******************************************************************\

Function: instrumentert::add_edges_assign
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void instrumentert::add_edges_assign(
  const cfgt::entryt &cfg_entry,
  const thread_eventst &thread_events)
{
  // anything other than an assignment or a function call containing
  // both reads and writes would be really strange...
  assert(cfg_entry.PC->is_assign() ||
         cfg_entry.PC->is_function_call());

  /* Write (Wa) */
  for(nodest::const_iterator w_it=thread_events.writes.begin();
      w_it!=thread_events.writes.end();
      ++w_it)
  {
    const unsigned w_node=*w_it;
    assert(map_vertex_gnode.find(w_node)!=map_vertex_gnode.end());
    const unsigned w_gnode=map_vertex_gnode[w_node];

    /* Read (Rb) */
    for(nodest::const_iterator r_it=thread_events.reads.begin();
        r_it!=thread_events.reads.end();
        ++r_it)
    {
      const unsigned r_node=*r_it;
      assert(map_vertex_gnode.find(r_node)!=map_vertex_gnode.end());
      const unsigned r_gnode=map_vertex_gnode[r_node];

      /* creates Read -po-> Write */
      DEBUG_MESSAGE(r_node<<"-po->"<<w_node);
      egraph.add_po_edge(r_node, w_node);
      egraph_alt.add_edge(r_gnode, w_gnode);
    }
  }
}

/*******************************************************************\

Function: instrumentert::add_com_edges
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void instrumentert::add_com_edges(
  const cfgt::entryt &cfg_entry,
  const thread_eventst &thread_events)
{
  /* Read (Rb) */
  for(nodest::const_iterator r_it=thread_events.reads.begin();
      r_it!=thread_events.reads.end();
      ++r_it)
  {
    const unsigned r_node=*r_it;
    const abstract_eventt &read_event=egraph[r_node];
    assert(map_vertex_gnode.find(r_node)!=map_vertex_gnode.end());
    const unsigned r_gnode=map_vertex_gnode[r_node];

    /* creates Read <-com-> Write ... */
    const std::pair<id2nodet::iterator,id2nodet::iterator>
      with_same_var = map_writes.equal_range(read_event.variable);
    for(id2nodet::iterator id_it=with_same_var.first;
        id_it!=with_same_var.second;
        id_it++)
      if(egraph[id_it->second].thread != read_event.thread)
      {
        DEBUG_MESSAGE(id_it->second<<"<-com->"<<r_node);
        std::map<unsigned,unsigned>::const_iterator entry=
          map_vertex_gnode.find(id_it->second);
        assert(entry!=map_vertex_gnode.end());
        egraph.add_com_edge(r_node,id_it->second);
        egraph_alt.add_edge(r_gnode,entry->second);
        egraph.add_com_edge(id_it->second,r_node);
        egraph_alt.add_edge(entry->second,r_gnode);
      }
      else if(id_it->second < r_node)
      {
        DEBUG_MESSAGE(id_it->second<<"-com->"<<r_node);
        std::map<unsigned,unsigned>::const_iterator entry=
          map_vertex_gnode.find(id_it->second);
        assert(entry!=map_vertex_gnode.end());
        egraph.add_com_edge(r_node,id_it->second);
        egraph_alt.add_edge(r_gnode,entry->second);
      }
  }

  /* Write (Wa) */
  for(nodest::const_iterator w_it=thread_events.writes.begin();
      w_it!=thread_events.writes.end();
      ++w_it)
  {
    const unsigned w_node=*w_it;
    const abstract_eventt &write_event=egraph[w_node];
    assert(map_vertex_gnode.find(w_node)!=map_vertex_gnode.end());
    const unsigned w_gnode=map_vertex_gnode[w_node];

    /* creates Write <-com-> Read */
    const std::pair<id2nodet::iterator,id2nodet::iterator>
      r_with_same_var=map_reads.equal_range(write_event.variable);
    for(id2nodet::iterator idr_it=r_with_same_var.first;
      idr_it!=r_with_same_var.second; idr_it++)
      if(egraph[idr_it->second].thread != write_event.thread)
      {
        DEBUG_MESSAGE(idr_it->second<<"<-com->"<<w_node);
        std::map<unsigned,unsigned>::const_iterator entry=
          map_vertex_gnode.find(idr_it->second);
        assert(entry!=map_vertex_gnode.end());
        egraph.add_com_edge(w_node,idr_it->second);
        egraph_alt.add_edge(w_gnode,entry->second);
        egraph.add_com_edge(idr_it->second,w_node);
        egraph_alt.add_edge(entry->second,w_gnode);
      }
      else if(idr_it->second < w_node)
      {
        DEBUG_MESSAGE(idr_it->second<<"-com->"<<w_node);
        std::map<unsigned,unsigned>::const_iterator entry=
          map_vertex_gnode.find(idr_it->second);
        assert(entry!=map_vertex_gnode.end());
        egraph.add_com_edge(w_node,idr_it->second);
        egraph_alt.add_edge(w_gnode,entry->second);
      }

    /* creates Write <-com-> Write */
    const std::pair<id2nodet::iterator,id2nodet::iterator>
      w_with_same_var=map_writes.equal_range(write_event.variable);
    for(id2nodet::iterator idw_it=w_with_same_var.first;
      idw_it!=w_with_same_var.second; idw_it++)
      if(egraph[idw_it->second].thread!=write_event.thread)
      {
        DEBUG_MESSAGE(idw_it->second<<"<-com->"<<w_node);
        std::map<unsigned,unsigned>::const_iterator entry=
          map_vertex_gnode.find(idw_it->second);
        assert(entry!=map_vertex_gnode.end());
        egraph.add_com_edge(w_node,idw_it->second);
        egraph_alt.add_edge(w_gnode,entry->second);
        egraph.add_com_edge(idw_it->second,w_node);
        egraph_alt.add_edge(entry->second,w_gnode);
      }
      else if(idw_it->second < w_node)
      {
        DEBUG_MESSAGE(idw_it->second<<"-com->"<<w_node);
        std::map<unsigned,unsigned>::const_iterator entry=
          map_vertex_gnode.find(idw_it->second);
        assert(entry!=map_vertex_gnode.end());
        egraph.add_com_edge(w_node,idw_it->second);
        egraph_alt.add_edge(w_gnode,entry->second);
      }
  }
}

/*******************************************************************\

Function: instrumentert::add_edges
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void instrumentert::add_edges(
  const cfgt::entryt &cfg_entry,
  const unsigned thread_nr,
  const thread_eventst &thread_events)
{
  if(!thread_events.reads.empty() ||
     !thread_events.writes.empty() ||
     !thread_events.fences.empty())
    add_po_edges(cfg_entry, thread_nr, thread_events);

  /* a:=b -o-> Rb -po-> Wa */
  if(!thread_events.reads.empty() &&
     !thread_events.writes.empty())
    add_edges_assign(cfg_entry, thread_events);

  if(!thread_events.reads.empty() ||
     !thread_events.writes.empty())
    add_com_edges(cfg_entry, thread_events);
}

/*******************************************************************\

Function: instrumentert::add_edges
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void instrumentert::add_edges()
{
  for(cfgt::entry_mapt::const_iterator it=cfg.entry_map.begin();
      it!=cfg.entry_map.end();
      ++it)
    for(std::map<unsigned, thread_eventst>::const_iterator
        t_it=it->second.events.begin();
        t_it!=it->second.events.end();
        ++t_it)
      add_edges(it->second, t_it->first, t_it->second);
}

/*******************************************************************\

Function: instrumentert::build_event_graph
  
  Inputs:
  
 Outputs:
  
 Purpose: goes through CFG and build a static abstract event
          graph overapproximating the read/write relations for any
          executions
  
\*******************************************************************/

unsigned instrumentert::build_event_graph(
  value_setst& value_sets,
  memory_modelt model,
  bool no_dependencies)
{
  if(!no_dependencies)
    std::cout << "Dependencies analysis enabled" << std::endl;

  cfg(goto_functions);

  forward_traverse_once(
    value_sets,
    model,
    no_dependencies);

  propagate_events_in_po();

  add_edges();

  std::vector<unsigned> subgraph_index;
  num_sccs = egraph_alt.SCCs(subgraph_index);
  assert(egraph_SCCs.empty());
  // the following instruction breaks strict aliasing rules, for some reason
  egraph_SCCs.resize(num_sccs, std::set<unsigned>());
  for(std::map<unsigned,unsigned>::const_iterator it=map_vertex_gnode.begin();
    it!=map_vertex_gnode.end();
    it++)
  {
    const unsigned sg = subgraph_index[it->second];
    egraph_SCCs[sg].insert(it->first);
  }

  std::cout<<"Number of threads detected: "<<max_thread<<std::endl;

  /* SCCs which could host critical cycles */
  unsigned interesting_sccs = 0;
  for(unsigned i=0; i<num_sccs; i++)
    if(egraph_SCCs[i].size()>3)
      interesting_sccs++;

  std::cout<<"Graph with "<<egraph_alt.size()<<" nodes has "
    <<interesting_sccs<<" interesting SCCs"<<std::endl;

  std::cout<<"Number of reads: "<<read_counter<<std::endl;
  std::cout<<"Number of writes: "<<write_counter<<std::endl;

  return max_thread;
}

/*******************************************************************\

Function: intrumentert::add_instr_to_interleaving

  Inputs:
     
 Outputs:
      
 Purpose: 

\*******************************************************************/

void inline instrumentert::add_instr_to_interleaving (
  goto_programt::instructionst::iterator it,
  goto_programt& interleaving)
{
  if(
    it->is_return() ||
    it->is_throw() ||
    it->is_catch() ||
    it->is_skip() ||
    it->is_dead() ||
    it->is_start_thread() ||
    it->is_end_thread()
  )
    return;

  if(
    it->is_atomic_begin() ||
    it->is_atomic_end()
  )
  {
    /* atomicity not checked here for the moment */
    return;
  }

  if(it->is_function_call())
  {
    /* function call not supported for the moment */
    return;
  }

  /* add this instruction to the interleaving */
  goto_programt::targett current_instruction = interleaving.add_instruction();
  goto_programt::instructiont new_instruction(*it);
  current_instruction->swap(new_instruction);
}

/*******************************************************************\

Function: instrumentert::is_cfg_spurious
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

bool instrumentert::is_cfg_spurious(const event_grapht::critical_cyclet& cyc)
{
  DEBUG_MESSAGE("spurious by CFG? ");
  goto_programt interleaving;

  for(event_grapht::critical_cyclet::const_iterator e_it=cyc.begin(); 
    e_it!=cyc.end() && ++e_it!=cyc.end(); ++e_it)
  {
    --e_it;

    const abstract_eventt& current_event = egraph[*e_it];
    const locationt& current_location = current_event.location;

    /* select relevant thread (po) -- or function contained in this thread */
    goto_programt* current_po=0;
    bool thread_found = false;

    Forall_goto_functions(f_it, goto_functions)
    {
      forall_goto_program_instructions(p_it, f_it->second.body)
        if(p_it->location==current_location)
        {
          current_po = &f_it->second.body;
          thread_found = true;
          break;
        }

      if(thread_found)
        break;
    }
    assert(current_po);

    const graph<abstract_eventt>::edgest& pos_cur = egraph.po_out(*e_it);
    const graph<abstract_eventt>::edgest& pos_next = egraph.po_out(*(++e_it));
    --e_it;

    bool exists_n = false;

    for(graph<abstract_eventt>::edgest::const_iterator edge_it=pos_cur.begin();
      edge_it!=pos_cur.end(); edge_it++)
    {
      if(pos_next.find(edge_it->first)!=pos_next.end())
      {
        exists_n = true;
        break;
      }
    }

    /* !exists n, has_po_edge(*e_it,n) /\ has_po_edge(*(++it--),n) */
    if((++e_it)!=cyc.end() || !exists_n)
    {
      --e_it;

      /* add this instruction to the interleaving */
      Forall_goto_program_instructions(i_it, *current_po)
        if(i_it->location==current_location)
        {
          /* add all the instructions of this line */
          for(goto_programt::instructionst::iterator same_loc=i_it;
            same_loc!=current_po->instructions.end() 
            && same_loc->location==i_it->location;
            same_loc++)
            add_instr_to_interleaving(same_loc, interleaving);
          break;
        }
    }
    else
    {
      --e_it;

      /* find the portion of the thread to add */
      const abstract_eventt& next_event = egraph[*(++e_it--)];
      const locationt& next_location = next_event.location;

      bool in_cycle = false;
      Forall_goto_program_instructions(it, *current_po)
      {
        if(it->location==current_location)
          in_cycle = true;

        /* do not add the last instruction now -- will be done at 
           the next iteration */
        if(it->location==next_location)
          break;

        if(in_cycle)
          add_instr_to_interleaving(it, interleaving);
      }
    }
  }

  /* if a goto points to a label outside from this interleaving, replace it 
     by an assert 0 */
  Forall_goto_program_instructions(int_it, interleaving)
    if(int_it->is_goto())
    {
      for(goto_programt::instructiont::targetst::const_iterator label=
        int_it->targets.begin();
        label!=int_it->targets.end();
        label++)
      {
        bool target_in_cycle = false;

        Forall_goto_program_instructions(targ, interleaving)
          if(targ==*label)
          {
            target_in_cycle = true;
            break;
          }

        if(!target_in_cycle)
        {
          goto_programt::instructiont new_inst;
          new_inst.make_assertion(false_exprt());
          int_it->swap(new_inst);
          // delete new_inst
          break;
        }
      }
    }

  /* now test whether this part of the code can exist */
  goto_function_templatet<goto_programt> one_interleaving;
  one_interleaving.body.copy_from(interleaving);

  std::pair<irep_idt,goto_function_templatet<goto_programt> > p(
    ID_main, one_interleaving);
  goto_functionst::function_mapt map;
  map.insert(p);

  goto_functionst this_interleaving;
  this_interleaving.function_map = map;
  optionst no_option;
  null_message_handlert no_message;
  
  #if 0
  bmct bmc(no_option, symbol_table, no_message);

  bool is_spurious = bmc.run(this_interleaving);
  
  DEBUG_MESSAGE("CFG:"<<is_spurious);
  return is_spurious;
  #else
  
  return false; // conservative for now
  #endif
}

/*******************************************************************\

Function: instrumentert::cfg_cycles_filter
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void instrumentert::cfg_cycles_filter()
{
  if(!set_of_cycles.empty())
  {
    for(std::set<event_grapht::critical_cyclet>::iterator 
      it=set_of_cycles.begin();
      it!=set_of_cycles.end();
    )
    {
      bool erased = false;
      std::set<event_grapht::critical_cyclet>::iterator next = it;
      ++next;
      if(is_cfg_spurious(*it))
      {
        erased = true;
        set_of_cycles.erase(it);
      }
      it = next;
      if(!erased)
        ++it;
    }
  }
  else if(num_sccs > 0)
  {
    for(unsigned i=0; i<num_sccs; i++)
      for(std::set<event_grapht::critical_cyclet>::iterator it=
        set_of_cycles_per_SCC[i].begin();
        it!=set_of_cycles_per_SCC[i].end();
      )
      {
        bool erased = false;
        std::set<event_grapht::critical_cyclet>::iterator next = it;
        ++next;
        if(is_cfg_spurious(*it))
        {
          erased = true;
          set_of_cycles_per_SCC[i].erase(it);
        }
        it = next;
        if(!erased)
          ++it;
      }
  }
  else
    DEBUG_MESSAGE("No cycle to filter");
}

/*******************************************************************\

Function: instrumentert::print_outputs
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void inline instrumentert::print_outputs_local(
  const std::set<event_grapht::critical_cyclet>& set,
  std::ofstream& dot,
  std::ofstream& ref,
  std::ofstream& output,
  std::ofstream& all,
  std::ofstream& table,
  memory_modelt model,
  bool hide_internals)
{
  /* to represent the po aligned in the dot */
  std::map<unsigned,std::set<unsigned> > same_po;
  unsigned max_thread = 0;
  unsigned colour = 0;

  /* to represent the files as clusters */
  std::map<irep_idt,std::set<unsigned> > same_file;

  /* to summarise in a table all the variables */
  std::map<std::string,std::string> map_id2var;
  std::map<std::string,std::string> map_var2id;

  for(std::set<event_grapht::critical_cyclet>::const_iterator it =
    set.begin(); it!=set.end(); it++)
  {
#ifdef PRINT_UNSAFES
    std::cout << it->print_unsafes() << std::endl;
#endif
    it->print_dot(dot,colour++,model);
    ref << it->print_name(model, hide_internals) << std::endl;
    output << it->print_output() << std::endl;
    all << it->print_all(model, map_id2var, map_var2id, hide_internals) 
      << std::endl;

    /* emphasises instrumented events */
    for(std::list<unsigned>::const_iterator it_e=it->begin();
      it_e!=it->end(); it_e++)
    {
      const abstract_eventt& ev = egraph[*it_e];

      if(render_po_aligned)
        same_po[ev.thread].insert(*it_e);
      if(render_by_function)
        same_file[ev.location.get_function()].insert(*it_e);
      else if(render_by_file)
        same_file[ev.location.get_file()].insert(*it_e);
      if(ev.thread>max_thread)
        max_thread = ev.thread;

      if(var_to_instr.find(ev.variable)!=var_to_instr.end()
        && id2loc.find(ev.variable)!=id2loc.end())
      {
        dot << ev.id << "[label=\"\\\\lb {" << ev.id << "}";
        dot << ev.get_operation() << "{" << ev.variable << "} {} @thread";
        dot << ev.thread << "\",color=red,shape=box];" << std::endl;
      }
    }
  }

  /* aligns events by po */
  if(render_po_aligned)
    for(unsigned i=0; i<=max_thread; i++)
      if(!same_po[i].empty())
      {
        dot << "{rank=same; thread_" << i 
          << "[shape=plaintext, label=\"thread " << i << "\"];";
        for(std::set<unsigned>::iterator it=same_po[i].begin(); 
          it!=same_po[i].end(); it++)
          dot << egraph[*it].id << ";";
        dot << "};" << std::endl;
      }

  /* clusters events by file/function */
  if(render_by_file || render_by_function)
    for(std::map<irep_idt,std::set<unsigned> >::const_iterator it=
      same_file.begin();
      it!=same_file.end(); it++)
    {
      dot << "subgraph cluster_" << irep_id_hash()(it->first) << "{" << std::endl;
      dot << "  label=\"" << it->first << "\";" << std::endl;
      for(std::set<unsigned>::const_iterator ev_it=it->second.begin();
        ev_it!=it->second.end(); ev_it++)
      {
        dot << "  " << egraph[*ev_it].id << ";" << std::endl;
      }
      dot << "};" << std::endl;
    }

  /* variable table for "all" */
  for(unsigned i=0; i<80; ++i) table << "-";
  for(std::map<std::string,std::string>::const_iterator m_it=map_id2var.begin();
    m_it!=map_id2var.end();
    ++m_it)
  {
    table << std::endl << "| " << m_it->first << " : " << m_it->second;
  }
  table << std::endl;
  for(unsigned i=0; i<80; ++i) table << "-";
  table << std::endl;
}

void instrumentert::print_outputs(memory_modelt model, bool hide_internals)
{
  std::ofstream dot;
  std::ofstream ref;
  std::ofstream output;
  std::ofstream all;
  std::ofstream table;

  dot.open("cycles.dot");
  ref.open("ref.txt");
  output.open("output.txt");
  all.open("all.txt");
  table.open("table.txt");

  dot << "digraph G {" << std::endl;
  dot << "nodesep=1; ranksep=1;" << std::endl;

  /* prints cycles in the different outputs */
  if(!set_of_cycles.empty())
    print_outputs_local(set_of_cycles, dot, ref, output, all, table,
      model,hide_internals);
  else if(num_sccs!=0)
  {
    for(unsigned i=0; i<num_sccs; i++)
    {
      std::ofstream local_dot;
      std::string name = "scc_" + i2string(i) + ".dot";
      local_dot.open(name.c_str());

      local_dot << "digraph G {" << std::endl;
      local_dot << "nodesep=1; ranksep=1;" << std::endl;
      print_outputs_local(set_of_cycles_per_SCC[i],local_dot,ref,output,all,
        table, model, hide_internals);
      local_dot << "}" << std::endl;
      local_dot.close();

      dot << i << "[label=\"SCC " << i << "\",link=\"" << "scc_" << i;
      dot << ".svg\"]" << std::endl;
    }
  }
  else
    DEBUG_MESSAGE("no cycles to output");

  dot << "}" << std::endl;

  dot.close();
  ref.close();
  output.close();
  all.close();
  table.close();
}

/*******************************************************************\

Function: instrumentert::collect_cycles_by_SCCs
  
  Inputs:
  
 Outputs:
  
 Purpose: Note: can be distributed (#define DISTRIBUTED)
  
\*******************************************************************/

#if 1
//#ifdef _WIN32
void instrumentert::collect_cycles_by_SCCs(memory_modelt model)
{
  unsigned scc = 0;
  set_of_cycles_per_SCC.resize(num_sccs,
    std::set<event_grapht::critical_cyclet>());
  for(std::vector<std::set<unsigned> >::const_iterator it=egraph_SCCs.begin();
    it!=egraph_SCCs.end(); it++)
    if(it->size()>=4)
      egraph.collect_cycles(set_of_cycles_per_SCC[scc++],model,*it);
}
#else
class pthread_argumentt
{
public:
  instrumentert& instr;
  memory_modelt mem;
  const std::set<unsigned>& filter;
  std::set<event_grapht::critical_cyclet>& cycles;

  pthread_argumentt(instrumentert& _instr,
    memory_modelt _mem, 
    const std::set<unsigned>& _filter,
    std::set<event_grapht::critical_cyclet>& _cycles)
    :instr(_instr),mem(_mem),filter(_filter),cycles(_cycles)
  {
  }
};

/* wraper */
void* collect_cycles_in_thread(void* arg)
{
  /* arguments */
  instrumentert& this_instrumenter = ((pthread_argumentt*) arg)->instr;
  memory_modelt model = ((pthread_argumentt*) arg)->mem;
  const std::set<unsigned>& filter = ((pthread_argumentt*) arg)->filter;
  std::set<event_grapht::critical_cyclet>& cycles = 
    ((pthread_argumentt*) arg)->cycles;

  this_instrumenter.egraph.collect_cycles(cycles, model, filter);

  return NULL;
}

void instrumentert::collect_cycles_by_SCCs(memory_modelt model)
{
  const unsigned number_of_sccs = num_sccs;
  std::set<unsigned> interesting_SCCs;

  unsigned scc = 0;
  pthread_t* threads = (pthread_t*)malloc((num_sccs+1)*sizeof(pthread_t));

  set_of_cycles_per_SCC.resize(num_sccs,
    std::set<event_grapht::critical_cyclet>());

  for(std::vector<std::set<unsigned> >::const_iterator it=egraph_SCCs.begin();
    it!=egraph_SCCs.end(); it++)
    if(it->size()>=4)
    {
      interesting_SCCs.insert(scc);
      pthread_argumentt arg(*this,model,*it,set_of_cycles_per_SCC[scc]);

      unsigned rc = pthread_create(&threads[scc++], NULL,
        collect_cycles_in_thread, (void*) &arg);

      std::cout<<(rc!=0?"Failure ":"Success ")
        <<"in creating thread for SCC #"<<scc-1<<std::endl;
    }

  for(unsigned i=0; i<number_of_sccs; i++)
    if(interesting_SCCs.find(i)!=interesting_SCCs.end())
    {
      unsigned rc = pthread_join(threads[i],NULL);
      std::cout<<(rc!=0?"Failure ":"Success ")
        <<"in joining thread for SCC #"<<i<<std::endl;
    }
}
#endif
