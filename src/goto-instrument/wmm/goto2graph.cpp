/*******************************************************************\

Module: Turns a goto-program into an abstract event graph

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

#include <vector>
#include <string>
#include <fstream>

#ifndef _WIN32
#include <cstdlib>
#include <pthread.h>
#endif

#include <prefix.h>
#include <cprover_prefix.h>
#include <options.h>
#include <message.h>
#include <i2string.h>

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

bool inline instrumentert::cfg_visitort::local(const irep_idt& i)
{
  return instrumenter.local(i);
}

/*******************************************************************\

Function: instrumentert::goto2graph_cfg
  
  Inputs:
  
 Outputs:
  
 Purpose: goes through CFG and build a static abstract event
          graph overapproximating the read/write relations for any
          executions
  
\*******************************************************************/

unsigned instrumentert::goto2graph_cfg(
  value_setst& value_sets,
  weak_memory_modelt model,
  bool no_dependencies)
{
  if(!no_dependencies)
    std::cout << "Dependencies analysis enabled" << std::endl;

  if(goto_functions.main_id()=="")
    throw "Main function not found";

  /* builds the graph following the CFG */
  cfg_visitort visitor(ns, *this);
  visitor.visit_cfg(value_sets, model, no_dependencies, 
    goto_functions.main_id());

  std::vector<unsigned> subgraph_index;
  num_sccs = egraph_alt.SCCs(subgraph_index);
  assert(egraph_SCCs.empty());
  egraph_SCCs.resize(num_sccs, std::set<unsigned>());
  for(std::map<unsigned,unsigned>::const_iterator it=map_vertex_gnode.begin();
    it!=map_vertex_gnode.end();
    it++)
  {
    const unsigned sg = subgraph_index[it->second];
    egraph_SCCs[sg].insert(it->first);
  }

  std::cout<<"Number of threads detected: "<<visitor.max_thread<<std::endl;

  /* SCCs which could host critical cycles */
  unsigned interesting_sccs = 0;
  for(unsigned i=0; i<num_sccs; i++)
    if(egraph_SCCs[i].size()>3)
      interesting_sccs++;

  std::cout<<"Graph with "<<egraph_alt.size()<<" nodes has "
    <<interesting_sccs<<" interesting SCCs"<<std::endl;

  std::cout<<"Number of reads: "<<visitor.read_counter<<std::endl;
  std::cout<<"Number of writes: "<<visitor.write_counter<<std::endl;

  return visitor.max_thread;
}

/*******************************************************************\

Function: instrumentert::cfg_visitort::visit_cfg_function
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void instrumentert::cfg_visitort::visit_cfg_function(
    /* value_sets and options */
    value_setst& value_sets,
    weak_memory_modelt model,
    bool no_dependencies,
    /* function to analyse */
    const irep_idt& function,
    /* incoming edges */
    const std::set<instrumentert::cfg_visitort::nodet>& initial_vertex,
    /* outcoming edges */
    std::set<instrumentert::cfg_visitort::nodet>& ending_vertex)
{
  /* flow: egraph */

  DEBUG_MESSAGE("visit function "<<function);

  if(function==CPROVER_PREFIX "initialize")
  {
    return;
  }

  /* goes through the function */
  Forall_goto_program_instructions(i_it, 
    instrumenter.goto_functions.function_map[function].body)
  {
    goto_programt::instructiont& instruction=*i_it;

    /* thread marking */
    if(instruction.is_start_thread())
    {
      max_thread=max_thread+1;
      coming_from=current_thread;
      current_thread=max_thread;
    }
    else if(instruction.is_end_thread())
      current_thread=coming_from;
    thread=current_thread;

    DEBUG_MESSAGE("visit instruction "<<instruction.type);

    if(instruction.is_start_thread() || instruction.is_end_thread())
    {
      /* break the flow */
      visit_cfg_thread();
    }

    /* a:=b -o-> Rb -po-> Wa */
    else if(instruction.is_assign())
    {
      visit_cfg_assign(value_sets, ns, i_it, no_dependencies);
    }

    else if(is_fence(instruction,instrumenter.ns))
    {
      visit_cfg_fence(i_it);
    }

    else if(model!=TSO && is_lwfence(instruction,instrumenter.ns))
    {
      visit_cfg_lwfence(i_it);
    }

    else if(model==TSO && is_lwfence(instruction, instrumenter.ns))
    {
      /* propagation */
      visit_cfg_skip(i_it);
    }

    else if(instruction.is_other() 
      && instruction.code.get_statement()==ID_fence)
    {
      visit_cfg_asm_fence(i_it);
    }

    else if(instruction.is_function_call())
    {
      visit_cfg_function_call(value_sets, i_it, model, no_dependencies);
    }

    else if(instruction.is_goto())
    {
      visit_cfg_goto(i_it);
    }

    else
    {
      /* propagates */
      visit_cfg_propagate(i_it);
    }
  }

  std::pair<unsigned,data_dpt> new_dp(thread, data_dp);
  egraph.map_data_dp.insert(new_dp);
  data_dp.print();

  if(instrumenter.goto_functions.function_map[function].body
    .instructions.size() <= 0)
  {
    /* empty set of ending edges */
  }
  else
  {
    goto_programt::instructionst::iterator it=instrumenter
      .goto_functions.function_map[function].body.instructions.end();
    --it;
    ending_vertex=in_pos[it];
  }  
}

/*******************************************************************\

Function: instrumentert::visit_cfg_propagate
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void inline instrumentert::cfg_visitort::visit_cfg_propagate(
  goto_programt::instructionst::iterator i_it)
{
  const goto_programt::instructiont& instruction=*i_it;
  /* propagation */
  in_pos[i_it].clear();
  for(target_sett::const_iterator prev=instruction.incoming_edges.begin();
    prev!=instruction.incoming_edges.end();
    ++prev)
    if(in_pos.find(*prev)!=in_pos.end())
      for(std::set<nodet>::const_iterator s_it=in_pos[*prev].begin();
        s_it!=in_pos[*prev].end();
        ++s_it)
        in_pos[i_it].insert(*s_it);
}

/*******************************************************************\

Function: instrumentert::visit_cfg_thread
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void instrumentert::cfg_visitort::visit_cfg_thread() const
{
}

/*******************************************************************\

Function: instrumentert::visit_cfg_goto
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void instrumentert::cfg_visitort::visit_cfg_goto(
  goto_programt::instructionst::iterator i_it)
{
  const goto_programt::instructiont& instruction=*i_it;

  /* propagates */
  visit_cfg_propagate(i_it);

  /* if back-edges, constructs them too:
     if goto to event, connects previously propagated events to it; 
     if not, we need to find which events AFTER the target are to
     be connected. We do a backward analysis. */
  if(instruction.is_backwards_goto())
  {
    DEBUG_MESSAGE("backward goto");          

    /* for each target of the goto */
    for(goto_programt::instructiont::targetst::const_iterator 
      targ=instruction.targets.begin();
      targ!=instruction.targets.end(); ++targ)
       /* if the target has already been covered by fwd analysis */
       if(in_pos.find(*targ)!=in_pos.end())
       {
         /* if in_pos was updated at this program point */
         if(updated.find(*targ)!=updated.end())
         {
           /* connects the previous nodes to those ones */
           for(std::set<nodet>::const_iterator to=in_pos[*targ].begin();
             to!=in_pos[*targ].end(); ++to)
             for(std::set<nodet>::const_iterator from=in_pos[i_it].begin();
               from!=in_pos[i_it].end(); ++from)
               if(from->first!=to->first)
               {
                 DEBUG_MESSAGE(from->first<<"-po->"<<to->first);
                 egraph.add_po_back_edge(from->first,to->first);
                 egraph_alt.add_edge(from->second,to->second);
               }
         }
         else
         {
           DEBUG_MESSAGE("else case");

           /* connects NEXT nodes following the targets -- bwd analysis */
           for(goto_programt::instructionst::iterator cur=i_it;
             cur!=*targ; --cur)
           {
             DEBUG_MESSAGE("i");

             for(std::set<goto_programt::instructiont::targett>::const_iterator 
               t=cur->incoming_edges.begin();
               t!=cur->incoming_edges.end(); ++t)
             {
               DEBUG_MESSAGE("t"); 

               if(in_pos.find(*t)!=in_pos.end() 
                 && updated.find(*t)!=updated.end())
               {
                 /* out_pos[*t].insert(in_pos[*t])*/
                 add_all_pos(it1, out_pos[*t], in_pos[*t]);
               }
               else if(in_pos.find(*t)!=in_pos.end())
               {
                 /* out_pos[*t].insert(in_pos[cur])*/
                 add_all_pos(it2, out_pos[*t], out_pos[cur]);
               }
             }
           }

           /* connects the previous nodes to those ones */
           if(out_pos.find(*targ)!=out_pos.end())
             for(std::set<nodet>::const_iterator to=out_pos[*targ].begin();
               to!=out_pos[*targ].end(); ++to)
               for(std::set<nodet>::const_iterator from=in_pos[i_it].begin();
                 from!=in_pos[i_it].end(); ++from)
                 if(from->first!=to->first)
                 {
#if 0
                   /* copies inner-graph twice */
                   const unsigned end_copy=egraph.copy_segment(from->first, 
                     to->first);
                   const unsigned end_copy_alt=egraph_alt.copy_segment(
                     from->second, to->second);
                   /* adds po back-edge */
                   DEBUG_MESSAGE(from->first<<"-po->"<<end_copy);
                   egraph.add_po_back_edge(from->first,end_copy);
                   egraph_alt.add_edge(from->second,end_copy_alt);
#endif
                   DEBUG_MESSAGE(from->first<<"-po->"<<to->first);
                   egraph.add_po_back_edge(from->first,to->first);
                   egraph_alt.add_edge(from->second,to->second);
                 }
         }
       }
  }
}

/*******************************************************************\

Function: intrumentert::visit_cfg_function_call

  Inputs:
     
 Outputs:
      
 Purpose: 

\*******************************************************************/

void instrumentert::cfg_visitort::visit_cfg_function_call(
  value_setst& value_sets, 
  goto_programt::instructionst::iterator i_it,
  weak_memory_modelt model,
  bool no_dependencies)
{
  const goto_programt::instructiont& instruction=*i_it;
  std::set<nodet> s;
  for(target_sett::const_iterator prev=instruction.incoming_edges.begin();
    prev!=instruction.incoming_edges.end(); ++prev)
    if(in_pos.find(*prev)!=in_pos.end())
      for(std::set<nodet>::const_iterator s_it=in_pos[*prev].begin();
        s_it!=in_pos[*prev].end(); ++s_it)
        s.insert(*s_it);

  const exprt& fun=to_code_function_call(instruction.code).function();
  const irep_idt& fun_id=to_symbol_expr(fun).get_identifier();
  enter_function(fun_id);
  visit_cfg_function(value_sets, model, no_dependencies, fun_id, s, in_pos[i_it]);
  updated.insert(i_it);
  leave_function(fun_id);
}

/*******************************************************************\

Function: instrumentert::visit_cfg_lwfence
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void instrumentert::cfg_visitort::visit_cfg_lwfence(
  goto_programt::instructionst::iterator i_it)
{
  const goto_programt::instructiont& instruction=*i_it;
  const abstract_eventt new_fence_event(abstract_eventt::Lwfence,
    thread, "f", instrumenter.unique_id++, instruction.location, false);
  const unsigned new_fence_node=egraph.add_node();
  egraph[new_fence_node](new_fence_event);
  const unsigned new_fence_gnode=egraph_alt.add_node();
  egraph_alt[new_fence_gnode]=new_fence_event;
  instrumenter.map_vertex_gnode.insert(
    std::make_pair(new_fence_node, new_fence_gnode));

  for(target_sett::const_iterator prev=instruction.incoming_edges.begin();
    prev!=instruction.incoming_edges.end(); ++prev)
    if(in_pos.find(*prev)!=in_pos.end())
      for(std::set<nodet>::const_iterator s_it=in_pos[*prev].begin();
        s_it!=in_pos[*prev].end(); ++s_it)
      {
        DEBUG_MESSAGE(s_it->first<<"-po->"<<new_fence_node);
        egraph.add_po_edge(s_it->first,new_fence_node);
        egraph_alt.add_edge(s_it->second,new_fence_gnode);
      }

  in_pos[i_it].clear();
  in_pos[i_it].insert(nodet(new_fence_node, new_fence_gnode));
  updated.insert(i_it);
}

/*******************************************************************\

Function: instrumentert::visit_cfg_lwfence
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void instrumentert::cfg_visitort::visit_cfg_asm_fence(
  goto_programt::instructionst::iterator i_it)
{
  const goto_programt::instructiont& instruction=*i_it;
  bool WRfence=instruction.code.get_bool(ID_WRfence);
  bool WWfence=instruction.code.get_bool(ID_WWfence);
  bool RRfence=instruction.code.get_bool(ID_RRfence);
  bool RWfence=instruction.code.get_bool(ID_RWfence);
  bool WWcumul=instruction.code.get_bool(ID_WWcumul);
  bool RRcumul=instruction.code.get_bool(ID_RRcumul);
  bool RWcumul=instruction.code.get_bool(ID_RWcumul);
  const abstract_eventt new_fence_event(abstract_eventt::ASMfence,
    thread, "asm", instrumenter.unique_id++, instruction.location,
    false, WRfence, WWfence, RRfence, RWfence, WWcumul, RWcumul, RRcumul);
  const unsigned new_fence_node=egraph.add_node();
  egraph[new_fence_node](new_fence_event);
  const unsigned new_fence_gnode=egraph_alt.add_node();
  egraph_alt[new_fence_gnode]=new_fence_event;
  instrumenter.map_vertex_gnode.insert(
    std::make_pair(new_fence_node, new_fence_gnode));

  for(target_sett::const_iterator prev=instruction.incoming_edges.begin();
    prev!=instruction.incoming_edges.end(); ++prev)
    if(in_pos.find(*prev)!=in_pos.end())
      for(std::set<nodet>::const_iterator s_it=in_pos[*prev].begin();
        s_it!=in_pos[*prev].end(); ++s_it)
      {
        DEBUG_MESSAGE(s_it->first<<"-po->"<<new_fence_node);
        egraph.add_po_edge(s_it->first,new_fence_node);
        egraph_alt.add_edge(s_it->second,new_fence_gnode);
      }

  in_pos[i_it].clear();
  in_pos[i_it].insert(nodet(new_fence_node, new_fence_gnode));
  updated.insert(i_it);
}

/*******************************************************************\

Function: instrumentert::visit_cfg_assign
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void instrumentert::cfg_visitort::visit_cfg_assign(
  value_setst& value_sets,
  namespacet& ns,
  goto_programt::instructionst::iterator& i_it,
  bool no_dependencies)
{
  goto_programt::instructiont& instruction=*i_it;

  /* Read (Rb) */
  rw_set_loct rw_set(ns, value_sets, i_it);

  unsigned previous=(unsigned)-1;
  unsigned previous_gnode=(unsigned)-1;

#if 0
  /* for the moment, use labels ASSERT in front of the assertions 
     to prevent them from being instrumented */
  if(instruction.is_assert())
    continue; // return;
  if(!instruction.labels.empty() && instruction.labels.front()=="ASSERT")
    continue; // return;
#endif

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
      thread, id2string(read), instrumenter.unique_id++,
      instruction.location, local(read));
    const unsigned new_read_node=egraph.add_node();
    egraph[new_read_node]=new_read_event;
    DEBUG_MESSAGE("new Read"<<read<<" @thread"
      <<(thread)<<"("<<instruction.location<<","
      <<(local(read)?"local":"shared")<<") #"<<new_read_node);

    const unsigned new_read_gnode=egraph_alt.add_node();
    egraph_alt[new_read_gnode]=new_read_event;
    instrumenter.map_vertex_gnode.insert(
    std::make_pair(new_read_node,new_read_gnode));

    /* creates ... -po-> Read */
    for(target_sett::const_iterator prev=instruction.incoming_edges.begin();
      prev!=instruction.incoming_edges.end();
      ++prev)
    {
      if(in_pos.find(*prev)!=in_pos.end())
        for(std::set<nodet>::const_iterator s_it=in_pos[*prev].begin();
          s_it!=in_pos[*prev].end();
          ++s_it)
        {
           DEBUG_MESSAGE(s_it->first<<"-po->"<<new_read_node);
           egraph.add_po_edge(s_it->first,new_read_node);
           egraph_alt.add_edge(s_it->second,new_read_gnode);
        }
    }

    map_reads.insert(id2node_pairt(read,new_read_node));
    previous=new_read_node;
    previous_gnode=new_read_gnode;

    /* creates Read <-com-> Write ... */
    const std::pair<id2nodet::iterator,id2nodet::iterator>
      with_same_var = map_writes.equal_range(read);
    for(id2nodet::iterator id_it=with_same_var.first;
      id_it!=with_same_var.second; id_it++)
      if(egraph[id_it->second].thread != new_read_event.thread)
      {
        DEBUG_MESSAGE(id_it->second<<"<-com->"<<new_read_node);
        std::map<unsigned,unsigned>::const_iterator entry=
          instrumenter.map_vertex_gnode.find(id_it->second);
        assert(entry!=instrumenter.map_vertex_gnode.end());
        egraph.add_com_edge(new_read_node,id_it->second);
        egraph_alt.add_edge(new_read_gnode,entry->second);
        egraph.add_com_edge(id_it->second,new_read_node);
        egraph_alt.add_edge(entry->second,new_read_gnode);
      }
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
      thread, id2string(write), instrumenter.unique_id++,
      instruction.location, local(write));
    const unsigned new_write_node=egraph.add_node();
    egraph[new_write_node](new_write_event);
    DEBUG_MESSAGE("new Write "<<write<<" @thread"<<(thread)
      <<"("<<instruction.location<<","
      << (local(write)?"local":"shared")<<") #"<<new_write_node);

    const unsigned new_write_gnode=egraph_alt.add_node();
    egraph_alt[new_write_gnode]=new_write_event;
    instrumenter.map_vertex_gnode.insert(
      std::pair<unsigned,unsigned>(new_write_node, new_write_gnode));

    /* creates Read -po-> Write */
    if(previous!=(unsigned)-1)
    {
      DEBUG_MESSAGE(previous<<"-po->"<<new_write_node);
      egraph.add_po_edge(previous,new_write_node);
      egraph_alt.add_edge(previous_gnode,new_write_gnode);
    }
    else
      for(target_sett::const_iterator prev=instruction.incoming_edges.begin();
        prev!=instruction.incoming_edges.end();
        ++prev)
      {
        if(in_pos.find(*prev)!=in_pos.end())
          for(std::set<nodet>::const_iterator s_it=in_pos[*prev].begin();
            s_it!=in_pos[*prev].end();
            ++s_it)
          {
            DEBUG_MESSAGE(s_it->first<<"-po->"<<new_write_node);
            egraph.add_po_edge(s_it->first,new_write_node);
            egraph_alt.add_edge(s_it->second,new_write_gnode);
          }
      }

    /* creates Write <-com-> Read */
    const std::pair<id2nodet::iterator,id2nodet::iterator>
      r_with_same_var=map_reads.equal_range(write);
    for(id2nodet::iterator idr_it=r_with_same_var.first;
      idr_it!=r_with_same_var.second; idr_it++)
      if(egraph[idr_it->second].thread != new_write_event.thread)
      {
        DEBUG_MESSAGE(idr_it->second<<"<-com->"<<new_write_node);
        std::map<unsigned,unsigned>::const_iterator entry=
          instrumenter.map_vertex_gnode.find(idr_it->second);
        assert(entry!=instrumenter.map_vertex_gnode.end());
        egraph.add_com_edge(new_write_node,idr_it->second);
        egraph_alt.add_edge(new_write_gnode,entry->second);
        egraph.add_com_edge(idr_it->second,new_write_node);
        egraph_alt.add_edge(entry->second,new_write_gnode);
      }

    /* creates Write <-com-> Write */
    const std::pair<id2nodet::iterator,id2nodet::iterator>
      w_with_same_var=map_writes.equal_range(write);
    for(id2nodet::iterator idw_it=w_with_same_var.first;
      idw_it!=w_with_same_var.second; idw_it++)
      if(egraph[idw_it->second].thread!=new_write_event.thread)
      {
        DEBUG_MESSAGE(idw_it->second<<"<-com->"<<new_write_node);
        std::map<unsigned,unsigned>::const_iterator entry=
          instrumenter.map_vertex_gnode.find(idw_it->second);
        assert(entry!=instrumenter.map_vertex_gnode.end());
        egraph.add_com_edge(new_write_node,idw_it->second);
        egraph_alt.add_edge(new_write_gnode,entry->second);
        egraph.add_com_edge(idw_it->second,new_write_node);
        egraph_alt.add_edge(entry->second,new_write_gnode);
      }

    map_writes.insert(id2node_pairt(write,new_write_node));
    previous = new_write_node;
    previous_gnode = new_write_gnode;
  }

  if(previous != (unsigned)-1)
  {
    in_pos[i_it].clear();
    in_pos[i_it].insert(nodet(previous,previous_gnode));
    updated.insert(i_it);
  }
  else
  {
    /* propagation */
    visit_cfg_skip(i_it);
  }

  /* data dependency analysis */
  if(!no_dependencies)
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

Function: instrumentert::visit_cfg_fence
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void instrumentert::cfg_visitort::visit_cfg_fence(
  goto_programt::instructionst::iterator i_it)
{
  const goto_programt::instructiont& instruction=*i_it;
  const abstract_eventt new_fence_event(abstract_eventt::Fence,
    thread, "F", instrumenter.unique_id++, instruction.location, false);
  const unsigned new_fence_node=egraph.add_node();
  egraph[new_fence_node](new_fence_event);
  const unsigned new_fence_gnode=egraph_alt.add_node();
  egraph_alt[new_fence_gnode]=new_fence_event;
  instrumenter.map_vertex_gnode.insert(
    std::make_pair(new_fence_node, new_fence_gnode));

  for(target_sett::const_iterator prev=instruction.incoming_edges.begin();
    prev!=instruction.incoming_edges.end();
    ++prev)
    if(in_pos.find(*prev)!=in_pos.end())
      for(std::set<nodet>::const_iterator s_it=in_pos[*prev].begin();
        s_it!=in_pos[*prev].end();
        ++s_it)
      {
        DEBUG_MESSAGE(s_it->first<<"-po->"<<new_fence_node);
        egraph.add_po_edge(s_it->first,new_fence_node);
        egraph_alt.add_edge(s_it->second,new_fence_gnode);
      }
#if 0
  std::set<nodet> s;
  s.insert(nodet(new_fence_node, new_fence_gnode));
  in_pos[i_it]=s;
  updated.insert(i_it);
#endif
  in_pos[i_it].clear();
  in_pos[i_it].insert(nodet(new_fence_node, new_fence_gnode));
  updated.insert(i_it);
}

/*******************************************************************\

Function: intrumentert::visit_cfg_skip

  Inputs:
     
 Outputs:
      
 Purpose: 

\*******************************************************************/

void instrumentert::cfg_visitort::visit_cfg_skip(
  goto_programt::instructionst::iterator i_it) 
{
  visit_cfg_propagate(i_it);
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
  weak_memory_modelt model,
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

void instrumentert::print_outputs(weak_memory_modelt model, bool hide_internals)
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
void instrumentert::collect_cycles_by_SCCs(weak_memory_modelt model)
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
  weak_memory_modelt mem;
  const std::set<unsigned>& filter;
  std::set<event_grapht::critical_cyclet>& cycles;

  pthread_argumentt(instrumentert& _instr,
    weak_memory_modelt _mem, 
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
  weak_memory_modelt model = ((pthread_argumentt*) arg)->mem;
  const std::set<unsigned>& filter = ((pthread_argumentt*) arg)->filter;
  std::set<event_grapht::critical_cyclet>& cycles = 
    ((pthread_argumentt*) arg)->cycles;

  this_instrumenter.egraph.collect_cycles(cycles, model, filter);

  return NULL;
}

void instrumentert::collect_cycles_by_SCCs(weak_memory_modelt model)
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
