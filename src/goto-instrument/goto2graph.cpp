/*******************************************************************\

Module: Turns a goto-program into an abstract event graph

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

#include <vector>
#include <string>

#include <glpk.h>
#include <string.h>

#include "goto2graph.h"

//#define DEBUG
//#define PRINT_UNSAFES

#ifdef DEBUG
#define DEBUG_MESSAGE(a) std::cout<<a<<std::endl
#else
#define DEBUG_MESSAGE(a)
#endif

#define DISTRIBUTED

#ifdef DISTRIBUTED
#include <cstdlib>
#include <pthread.h>
#endif

/*******************************************************************\

Function: instrumentert::local

  Inputs:
 
 Outputs:
 
 Purpose: is local variable?

\*******************************************************************/

bool inline instrumentert::local(const irep_idt& id)
{
  namespacet ns(context);

  std::string identifier = id2string(id);

  if(has_prefix(identifier, "symex_invalid"))
  {
    /* should however be false to be sound, but symex_invalid
       are errors in the input code */
    return true;
  }

  if(identifier=="c::__CPROVER_alloc" ||
    identifier=="c::__CPROVER_alloc_size" ||
    identifier=="c::stdin" ||
    identifier=="c::stdout" ||
    identifier=="c::stderr" ||
    identifier=="c::sys_nerr" ||
    has_prefix(identifier, "__unbuffered_") ||
    has_prefix(identifier, "c::__unbuffered_") ||
    has_infix(identifier, "$tmp_guard"))
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

  namespacet ns(context);

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

Function: instrumentert::cfg_visitort::visit_cfg_impl
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

const std::set<instrumentert::cfg_visitort::nodet>& 
  instrumentert::cfg_visitort::visit_cfg_impl(
    value_setst& value_sets,
    weak_memory_modelt model,
    bool no_dependencies,
    const irep_idt& function,
    const std::set<instrumentert::cfg_visitort::nodet>& initial_vertex)
{
  DEBUG_MESSAGE("visit function "<<function);

  if(function==CPROVER_PREFIX "initialize")
  {
      static std::set<nodet> s;
      return s;
  }

  Forall_goto_program_instructions(i_it, 
    instrumenter.goto_functions.function_map[function].body)
  {
    goto_programt::instructiont& instruction = *i_it;

    /* thread marking */
    if(instruction.is_start_thread())
    {
      max_thread = max_thread+1;
      coming_from = current_thread;
      current_thread = max_thread;
    }
    else if(instruction.is_end_thread())
      current_thread = coming_from;
    thread = current_thread;

    DEBUG_MESSAGE("visit instruction "<<instruction.type);

    if(instruction.is_start_thread()
      || instruction.is_end_thread())
    {
      /* break the flow */
    }

    /* a:=b -o-> Rb -po-> Wa */
    else if(instruction.is_assign())
    {
      /* Read (Rb) */
      rw_set_loct rw_set(ns, value_sets, i_it);

      unsigned previous = (unsigned)-1;
      unsigned previous_gnode = (unsigned)-1;

#if 0
      /* for the moment, use labels ASSERT in front of the assertions 
         to prevent them from being instrumented */
      if(instruction.is_assert())
        continue;
      if(!instruction.labels.empty() && instruction.labels.front()=="ASSERT")
        continue;
#endif

      forall_rw_set_r_entries(r_it, rw_set)
      {
        /* creates Read:
           read is the irep_id of the read in the code;
           new_read_event is the corresponding abstract event;
           new_read_node is the node in the graph */
        const irep_idt& read = r_it->second.object;

        /* skip local variables */
        if(local(read) || has_infix(id2string(read),"invalid_object"))
          continue;

        read_counter++;

        const abstract_eventt new_read_event(abstract_eventt::Read,
          thread, id2string(read), instrumenter.unique_id++,
          instruction.location, local(read));
        const unsigned new_read_node = egraph.add_node();
        egraph[new_read_node] = new_read_event;
        DEBUG_MESSAGE("new Read"<<read<<" @thread"
          <<(thread)<<"("<<instruction.location<<","
          <<(local(read)?"local":"shared")<<") #"<<new_read_node);

        const unsigned new_read_gnode = egraph_alt.add_node();
        egraph_alt[new_read_gnode] = new_read_event;
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
        previous = new_read_node;
        previous_gnode = new_read_gnode;

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
        if(local(write) || has_infix(id2string(write),"invalid_object"))
          continue;

        write_counter++;

        /* creates Write */
        const abstract_eventt new_write_event(abstract_eventt::Write,
          thread, id2string(write), instrumenter.unique_id++,
          instruction.location, local(write));
        const unsigned new_write_node = egraph.add_node();
        egraph[new_write_node](new_write_event);
        DEBUG_MESSAGE("new Write "<<write<<" @thread"<<(thread)
          <<"("<<instruction.location<<","
          << (local(write)?"local":"shared")<<") #"<<new_write_node);

        const unsigned new_write_gnode = egraph_alt.add_node();
        egraph_alt[new_write_gnode] = new_write_event;
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
          for(target_sett::const_iterator prev=
            instruction.incoming_edges.begin();
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
           if(egraph[idr_it->second].thread!=new_write_event.thread)
           {
             DEBUG_MESSAGE(idr_it->second<<"<-com->"<<new_write_node);
             std::map<unsigned,unsigned>::const_iterator entry =
               instrumenter.map_vertex_gnode.find(idr_it->second);
             assert(entry!=instrumenter.map_vertex_gnode.end());
             egraph.add_com_edge(new_write_node,idr_it->second);
             egraph_alt.add_edge(new_write_gnode,entry->second);
             egraph.add_com_edge(idr_it->second,new_write_node);
             egraph_alt.add_edge(entry->second,new_write_gnode);
           }

         /* creates Write <-com-> Write */
         const std::pair<id2nodet::iterator,id2nodet::iterator>
           w_with_same_var = map_writes.equal_range(write);
         for(id2nodet::iterator idw_it=w_with_same_var.first;
           idw_it!=w_with_same_var.second; idw_it++)
           if(egraph[idw_it->second].thread!=new_write_event.thread)
           {
             DEBUG_MESSAGE(idw_it->second<<"<-com->"<<new_write_node);
             std::map<unsigned,unsigned>::const_iterator entry =
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
         std::set<nodet> s;
         s.insert(nodet(previous,previous_gnode));
         in_pos[i_it]=s;
         updated.insert(i_it);
       }
       else
       {
        /* propagation */
        std::set<nodet> s;
        for(target_sett::const_iterator prev=instruction.incoming_edges.begin();
          prev!=instruction.incoming_edges.end();
          ++prev)
          if(in_pos.find(*prev)!=in_pos.end())
            for(std::set<nodet>::const_iterator s_it=in_pos[*prev].begin();
              s_it!=in_pos[*prev].end();
              ++s_it)
              s.insert(*s_it);
        in_pos[i_it] = s;
       }

       /* data dependency analysis */
       if(!no_dependencies)
       {
         forall_rw_set_w_entries(write_it, rw_set)
           forall_rw_set_r_entries(read_it, rw_set)
           {
             const irep_idt& write = write_it->second.object;
             const irep_idt& read = read_it->second.object;
             DEBUG_MESSAGE("dp: Write:"<<write<<"; Read:"<<read);
             const data_dpt::datat read_p(read,instruction.location);
             const data_dpt::datat write_p(write,instruction.location);
             data_dp.dp_analysis(read_p,local(read),write_p,local(write));
           }
         data_dp.dp_merge();

         forall_rw_set_r_entries(read2_it, rw_set)
           forall_rw_set_r_entries(read_it, rw_set)
           {
             const irep_idt& read2 = read2_it->second.object;
             const irep_idt& read = read_it->second.object;
             if(read2==read)
               continue;
             const data_dpt::datat read_p(read,instruction.location);
             const data_dpt::datat read2_p(read2,instruction.location);
             data_dp.dp_analysis(read_p,local(read),read2_p,local(read2));
           }
         data_dp.dp_merge();
       }
     }
     else if(is_fence(instruction,instrumenter.context))
     {
       const abstract_eventt new_fence_event(abstract_eventt::Fence,
         thread, "F", instrumenter.unique_id++, 
         instruction.location,
         false);
       const unsigned new_fence_node = egraph.add_node();
       egraph[new_fence_node](new_fence_event);
       const unsigned new_fence_gnode = egraph_alt.add_node();
       egraph_alt[new_fence_gnode] = new_fence_event;
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

        std::set<nodet> s;
        s.insert(nodet(new_fence_node, new_fence_gnode));
        in_pos[i_it]=s;
        updated.insert(i_it);
      }
      else if(model!=TSO && is_lwfence(instruction,instrumenter.context))
      {
        const abstract_eventt new_fence_event(abstract_eventt::Lwfence,
          thread, "f", instrumenter.unique_id++, 
          instruction.location,
          false);
        const unsigned new_fence_node = egraph.add_node();
        egraph[new_fence_node](new_fence_event);
        const unsigned new_fence_gnode = egraph_alt.add_node();
        egraph_alt[new_fence_gnode] = new_fence_event;
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

        std::set<nodet> s;
        s.insert(nodet(new_fence_node, new_fence_gnode));
        in_pos[i_it]=s;
        updated.insert(i_it);
      }

      else if(model==TSO && is_lwfence(instruction,instrumenter.context))
      {
        /* propagation */
        std::set<nodet> s;
        for(target_sett::const_iterator prev=instruction.incoming_edges.begin();
          prev!=instruction.incoming_edges.end();
          ++prev)
          if(in_pos.find(*prev)!=in_pos.end())
            for(std::set<nodet>::const_iterator s_it=in_pos[*prev].begin();
              s_it!=in_pos[*prev].end();
              ++s_it)
              s.insert(*s_it);
        in_pos[i_it] = s;
      }

      else if(instruction.is_other()
        && instruction.code.get_statement()==ID_fence)
      {
        bool WRfence = instruction.code.get_bool(ID_WRfence);
        bool WWfence = instruction.code.get_bool(ID_WWfence);
        bool RRfence = instruction.code.get_bool(ID_RRfence);
        bool RWfence = instruction.code.get_bool(ID_RWfence);
        bool WWcumul = instruction.code.get_bool(ID_WWcumul);
        bool RRcumul = instruction.code.get_bool(ID_RRcumul);
        bool RWcumul = instruction.code.get_bool(ID_RWcumul);
        const abstract_eventt new_fence_event(abstract_eventt::ASMfence,
          thread, "asm", instrumenter.unique_id++, 
          instruction.location,
          false, WRfence, WWfence, RRfence, RWfence, WWcumul, RWcumul,
          RRcumul
          );
        const unsigned new_fence_node = egraph.add_node();
        egraph[new_fence_node](new_fence_event);
        const unsigned new_fence_gnode = egraph_alt.add_node();
        egraph_alt[new_fence_gnode] = new_fence_event;
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

        std::set<nodet> s;
        s.insert(nodet(new_fence_node, new_fence_gnode));
        in_pos[i_it]=s;
        updated.insert(i_it);
      }

      else if(instruction.is_function_call())
      {
        std::set<nodet> s;
        for(target_sett::const_iterator prev=instruction.incoming_edges.begin();
          prev!=instruction.incoming_edges.end();
          ++prev)
          if(in_pos.find(*prev)!=in_pos.end())
            for(std::set<nodet>::const_iterator s_it=in_pos[*prev].begin();
              s_it!=in_pos[*prev].end();
              ++s_it)
              s.insert(*s_it);

        const exprt& fun = to_code_function_call(instruction.code).function();
        const std::set<nodet>& ret = visit_cfg_impl(value_sets, model, 
          no_dependencies, to_symbol_expr(fun).get_identifier(), s);
        
        in_pos[i_it] = ret;
        updated.insert(i_it);
      }

      else if(instruction.is_goto())
      {
        /* propagates */
        std::set<nodet> s;
        for(target_sett::const_iterator prev=instruction.incoming_edges.begin();
          prev!=instruction.incoming_edges.end();
          ++prev)
          if(in_pos.find(*prev)!=in_pos.end())
            for(std::set<nodet>::const_iterator s_it=in_pos[*prev].begin();
              s_it!=in_pos[*prev].end();
              ++s_it)
              s.insert(*s_it);
        in_pos[i_it] = s;

        /* if back-edges, constructs them too: */
        /* if goto to event, connects previously propagated events to it; 
           if not, we need to find which events AFTER the target are to
           be connected. We do a backward analysis. */
        if(instruction.is_backwards_goto())
        {
          DEBUG_MESSAGE("backward goto");          

          /* for each target of the goto */
          for(goto_programt::instructiont::targetst::const_iterator 
            targ=instruction.targets.begin();
            targ!=instruction.targets.end();
            ++targ)
            /* if the target has already been covered by fwd analysis */
            if(in_pos.find(*targ)!=in_pos.end())
            {
              /* if in_pos was updated at this program point */
              if(updated.find(*targ)!=updated.end())
              {
                /* connects the previous nodes to those ones */
                for(std::set<nodet>::const_iterator to=in_pos[*targ].begin();
                  to!=in_pos[*targ].end();
                  ++to)
                  for(std::set<nodet>::const_iterator from=s.begin();
                    from!=s.end();
                    ++from)
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
                for(goto_programt::instructionst::iterator 
                  cur=i_it;
                  cur!=*targ;//*targ;
                  --cur)
                {
                  DEBUG_MESSAGE("i");

                  for(std::set<goto_programt::instructiont::targett>
                    ::const_iterator t=cur->incoming_edges.begin();
                    t!=cur->incoming_edges.end();
                    ++t)
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
                  to!=out_pos[*targ].end();
                  ++to)
                  for(std::set<nodet>::const_iterator from=s.begin();
                    from!=s.end();
                    ++from)
                  if(from->first!=to->first)
                  {
                    DEBUG_MESSAGE(from->first<<"-po->"<<to->first);
                    egraph.add_po_back_edge(from->first,to->first);
                    egraph_alt.add_edge(from->second,to->second);
                  }

              }
            }
        }
      }

      else
      {
        /* propagates */
        std::set<nodet> s;
        for(target_sett::const_iterator prev=instruction.incoming_edges.begin();
          prev!=instruction.incoming_edges.end();
          ++prev)
          if(in_pos.find(*prev)!=in_pos.end())
            for(std::set<nodet>::const_iterator s_it=in_pos[*prev].begin();
              s_it!=in_pos[*prev].end();
              ++s_it)
              s.insert(*s_it);
        in_pos[i_it] = s;
      }
    }

    std::pair<unsigned,data_dpt> new_dp(thread, data_dp);
    egraph.map_data_dp.insert(new_dp);
    data_dp.print();

    if(instrumenter.goto_functions.function_map[function].body
      .instructions.size() <= 0)
    {
      static std::set<nodet> s;
      return s;
    }
    else
    {
      goto_programt::instructionst::iterator it = instrumenter
        .goto_functions.function_map[function].body.instructions.end();
      --it;
      return in_pos[it];
    }  
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
    goto_programt* current_po;
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
  bmct bmc(no_option, context, no_message);

  bool is_spurious = bmc.run(this_interleaving);
  DEBUG_MESSAGE("CFG:"<<is_spurious);
  return is_spurious;
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

Function: instrumentert::instrument_all
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void inline instrumentert::instrument_all_inserter(
  const std::set<event_grapht::critical_cyclet>& set_of_cycles)
{
  for(std::set<event_grapht::critical_cyclet>::const_iterator
    it=(set_of_cycles).begin();
    it!=(set_of_cycles).end(); it++)
  {
    for(std::set<event_grapht::critical_cyclet::delayt>::const_iterator
      p_it=it->unsafe_pairs.begin();
      p_it!=it->unsafe_pairs.end(); p_it++)
    {
      const abstract_eventt& first_ev = egraph[p_it->first];
      var_to_instr.insert(first_ev.variable);
      id2loc.insert(
        std::pair<irep_idt,locationt>(first_ev.variable,first_ev.location));
      if(!p_it->is_po)
      {
        const abstract_eventt& second_ev = egraph[p_it->second];
        var_to_instr.insert(second_ev.variable);
        id2loc.insert(
          std::pair<irep_idt,locationt>(second_ev.variable,second_ev.location));
      }
    }
  }
}

void instrumentert::instrument_all()
{
  var_to_instr.clear();
  id2loc.clear();
  id2cycloc.clear();

  if(!set_of_cycles.empty())
  {  
    instrument_all_inserter(set_of_cycles);
  }
  else if(num_sccs!=0)
  {
    for(unsigned i=0; i<num_sccs; i++)
    {
      instrument_all_inserter(set_of_cycles_per_SCC[i]); 
    }
  }
  else
    DEBUG_MESSAGE("no cycles to instrument");
}

/*******************************************************************\

Function: instrumentert::instrument_one_event_per_cycle
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void inline instrumentert::instrument_one_event_per_cycle_inserter(
  const std::set<event_grapht::critical_cyclet>& set_of_cycles)
{
  /* to keep track of the delayed pair, and to avoid the instrumentation
     of two pairs in a same cycle */
  std::set<event_grapht::critical_cyclet::delayt> delayed;

  for(std::set<event_grapht::critical_cyclet>::iterator
    it=set_of_cycles.begin();
    it!=set_of_cycles.end(); it++)
  {
    /* cycle with already a delayed pair? */
    bool next = false;
    for(std::set<event_grapht::critical_cyclet::delayt>::iterator
      p_it=it->unsafe_pairs.begin();
      p_it!=it->unsafe_pairs.end(); p_it++)
    {
      if(delayed.find(*p_it)!=delayed.end())
      {
        next = true;
        break;
      }
    }

    if(next)
      continue;  

    /* instruments the first pair */
    for(std::set<event_grapht::critical_cyclet::delayt>::iterator
      p_it=it->unsafe_pairs.begin();
      p_it!=it->unsafe_pairs.end(); p_it++)
    {
      delayed.insert(*p_it);
      const abstract_eventt& first_ev = egraph[p_it->first];
      var_to_instr.insert(first_ev.variable);
      id2loc.insert(
        std::pair<irep_idt,locationt>(first_ev.variable,first_ev.location));
      if(!p_it->is_po)
      {
        const abstract_eventt& second_ev = egraph[p_it->second];
        var_to_instr.insert(second_ev.variable);
        id2loc.insert(
          std::pair<irep_idt,locationt>(second_ev.variable,second_ev.location));
      }
      break;
    }
  }
}

void instrumentert::instrument_one_event_per_cycle()
{
  var_to_instr.clear();
  id2loc.clear();
  id2cycloc.clear();

  if(!set_of_cycles.empty())
    instrument_one_event_per_cycle_inserter(set_of_cycles);
  else if(num_sccs!=0)
  {
    for(unsigned i=0; i<num_sccs; i++)
      instrument_one_event_per_cycle_inserter(set_of_cycles_per_SCC[i]);
  }
  else
    DEBUG_MESSAGE("no cycles to instrument");
}

/*******************************************************************\

Function: instrumentert::instrument_one_read_per_cycle
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void inline instrumentert::instrument_one_read_per_cycle_inserter(
  const std::set<event_grapht::critical_cyclet>& set_of_cycles)
{
  /* TODO */
}

void instrumentert::instrument_one_read_per_cycle()
{
  var_to_instr.clear();
  id2loc.clear();
  id2cycloc.clear();

  if(!set_of_cycles.empty())
    instrument_one_read_per_cycle_inserter(set_of_cycles);
  else if(num_sccs!=0)
  {
    for(unsigned i=0; i<num_sccs; i++)
      instrument_one_read_per_cycle_inserter(set_of_cycles_per_SCC[i]);
  }
  else
    DEBUG_MESSAGE("no cycles to instrument");
}

/*******************************************************************\

Function: instrumentert::instrument_one_write_per_cycle
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void inline instrumentert::instrument_one_write_per_cycle_inserter(
  const std::set<event_grapht::critical_cyclet>& set_of_cycles)
{
  /* TODO */
}

void instrumentert::instrument_one_write_per_cycle()
{
  var_to_instr.clear();
  id2loc.clear();
  id2cycloc.clear();

  if(!set_of_cycles.empty())
    instrument_one_write_per_cycle_inserter(set_of_cycles);
  else if(num_sccs!=0)
  {
    for(unsigned i=0; i<num_sccs; i++)
      instrument_one_write_per_cycle_inserter(set_of_cycles_per_SCC[i]);
  }
  else
    DEBUG_MESSAGE("no cycles to instrument");
}

/*******************************************************************\

Function: instrumentert::instrument_minimum_interference
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

unsigned inline instrumentert::d(
  const event_grapht::critical_cyclet::delayt& e) 
{
  if(egraph[e.first].operation==abstract_eventt::Write)
    return 1;
  else if(egraph[e.second].operation==abstract_eventt::Write
    || !e.is_po)
    return 2;
  else
    return 3;
}



void inline instrumentert::instrument_minimum_interference_inserter(
  const std::set<event_grapht::critical_cyclet>& set_of_cycles)
{
  /* Idea:
     We solve this by a linear programming approach, 
     using for instance glpk lib.

     Input: the edges to instrument E, the cycles C_j
     Pb: min sum_{e_i in E} d(e_i).x_i
         s.t. for all j, sum_{e_i in C_j} >= 1,
       where e_i is a pair to potentially instrument, 
       x_i is a Boolean stating whether we instrument
       e_i, and d() is the cost of an instrumentation.
     Output: the x_i, saying which pairs to instrument

     For this instrumentation, we propose:
     d(poW*)=1
     d(poRW)=d(rfe)=2
     d(poRR)=3

     This function can be refined with the actual times 
     we get in experimenting the different pairs in a 
     single IRIW.
  */
  
  /* first, identify all the unsafe pairs */
  std::set<event_grapht::critical_cyclet::delayt> edges;
  for(std::set<event_grapht::critical_cyclet>::iterator 
    C_j=set_of_cycles.begin();
    C_j!=set_of_cycles.end();
    ++C_j)
    for(std::set<event_grapht::critical_cyclet::delayt>::const_iterator e_i=
      C_j->unsafe_pairs.begin();
      e_i!=C_j->unsafe_pairs.end();
      ++e_i)
      edges.insert(*e_i);

  glp_prob* lp;
  glp_iocp parm;
  glp_init_iocp(&parm);
  parm.msg_lev = GLP_MSG_OFF;
  parm.presolve = GLP_ON;

  lp = glp_create_prob();
  glp_set_prob_name(lp, "instrumentation optimisation");
  glp_set_obj_dir(lp, GLP_MIN);
  
  DEBUG_MESSAGE("edges: "<<edges.size()<<" cycles:"<<set_of_cycles.size());

  /* sets the variables and coefficients */
  glp_add_cols(lp, edges.size());
  unsigned i = 0;
  for(std::set<event_grapht::critical_cyclet::delayt>::iterator 
    e_i=edges.begin();
    e_i!=edges.end();
    ++e_i)
  {
    ++i;
    std::string name = "e_"+i2string(i);
    glp_set_col_name(lp, i, name.c_str());
    glp_set_col_bnds(lp, i, GLP_LO, 0.0, 0.0);
    glp_set_obj_coef(lp, i, d(*e_i));
    glp_set_col_kind(lp, i, GLP_BV);
  }

  /* sets the constraints (soundness): one per cycle */
  glp_add_rows(lp, set_of_cycles.size());
  i = 0;
  for(std::set<event_grapht::critical_cyclet>::iterator
    C_j=set_of_cycles.begin();
    C_j!=set_of_cycles.end();
    ++C_j)
  {
    ++i;
    std::string name = "C_"+i2string(i);
    glp_set_row_name(lp, i, name.c_str());
    glp_set_row_bnds(lp, i, GLP_LO, 1.0, 0.0); /* >= 1*/
  }

  const unsigned mat_size = set_of_cycles.size()*edges.size();
  DEBUG_MESSAGE("size of the system: " << mat_size);
  int* imat = (int*)malloc(sizeof(int)*(mat_size+1));
  int* jmat = (int*)malloc(sizeof(int)*(mat_size+1));
  double* vmat = (double*)malloc(sizeof(double)*(mat_size+1));
  
  /* fills the constraints coeff */
  unsigned col = 1;
  unsigned row = 1;
  i = 1;
  for(std::set<event_grapht::critical_cyclet::delayt>::iterator
    e_i=edges.begin();
    e_i!=edges.end();
    ++e_i)
  {
    row = 1;
    for(std::set<event_grapht::critical_cyclet>::iterator
      C_j=set_of_cycles.begin();
      C_j!=set_of_cycles.end();
      ++C_j)
    {
      imat[i] = row;
      jmat[i] = col;
      if(C_j->unsafe_pairs.find(*e_i)!=C_j->unsafe_pairs.end())
        vmat[i] = 1.0;
      else
        vmat[i] = 0.0;
      i++;
      row++;
    }
    col++;
  }

#ifdef DEBUG
  for(i=1; i<=mat_size; ++i)
    std::cout<<i<<"["<<imat[i]<<","<<jmat[i]<<"]="<<vmat[i]<<std::endl;
#endif

  /* solves MIP by branch-and-cut */
  glp_load_matrix(lp, mat_size, imat, jmat, vmat);
  glp_intopt(lp, &parm);

  /* loads results (x_i) */
  std::cout << "minimal cost: " << glp_mip_obj_val(lp) << std::endl;
  i = 0;
  for(std::set<event_grapht::critical_cyclet::delayt>::iterator
    e_i=edges.begin();
    e_i!=edges.end();
    ++e_i)
  {
    ++i;
    if(glp_mip_col_val(lp, i)>=1)
    {
      const abstract_eventt& first_ev = egraph[e_i->first];
      var_to_instr.insert(first_ev.variable);
      id2loc.insert(
        std::pair<irep_idt,locationt>(first_ev.variable,first_ev.location));
      if(!e_i->is_po)
      {
        const abstract_eventt& second_ev = egraph[e_i->second];
        var_to_instr.insert(second_ev.variable);
        id2loc.insert(
          std::pair<irep_idt,locationt>(second_ev.variable,second_ev.location));
      }
    }
  }

  glp_delete_prob(lp);
  free(imat);
  free(jmat);
  free(vmat);
}

void instrumentert::instrument_minimum_interference()
{
  var_to_instr.clear();
  id2loc.clear();
  id2cycloc.clear();

  if(!set_of_cycles.empty())
    instrument_minimum_interference_inserter(set_of_cycles);
  else if(num_sccs!=0)
  {
    for(unsigned i=0; i<num_sccs; i++)
      instrument_minimum_interference_inserter(set_of_cycles_per_SCC[i]);
  }
  else
    DEBUG_MESSAGE("no cycles to instrument");
}

/*******************************************************************\

Function: instrumentert::instrument_my_events
  
  Inputs:
  
 Outputs:
  
 Purpose:
  
\*******************************************************************/

void inline instrumentert::instrument_my_events_inserter(
  const std::set<event_grapht::critical_cyclet>& set,
  const std::set<unsigned>& my_events)
{
  for(std::set<event_grapht::critical_cyclet>::const_iterator
    it=set.begin();
    it!=set.end(); it++)
  {
    for(std::set<event_grapht::critical_cyclet::delayt>::const_iterator
      p_it=it->unsafe_pairs.begin();
      p_it!=it->unsafe_pairs.end(); p_it++)
    {
      if(my_events.find(p_it->first)!=my_events.end())
      {
        const abstract_eventt& first_ev = egraph[p_it->first];
        var_to_instr.insert(first_ev.variable);
        id2loc.insert(
          std::pair<irep_idt,locationt>(first_ev.variable,first_ev.location));
        if(!p_it->is_po && my_events.find(p_it->second)!=my_events.end())
        {
          const abstract_eventt& second_ev = egraph[p_it->second];
          var_to_instr.insert(second_ev.variable);
          id2loc.insert(
            std::pair<irep_idt,locationt>(second_ev.variable,
              second_ev.location));
        }
      }
    }
  }
}

void instrumentert::instrument_my_events(const std::set<unsigned>& my_events)
{
  var_to_instr.clear();
  id2loc.clear();
  id2cycloc.clear();

  if(!set_of_cycles.empty())
    instrument_my_events_inserter(set_of_cycles, my_events);
  else if(num_sccs!=0)
  {
    for(unsigned i=0; i<num_sccs; i++)
      instrument_my_events_inserter(set_of_cycles_per_SCC[i], my_events);
  }
  else
    DEBUG_MESSAGE("no cycles to instrument");
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
  weak_memory_modelt model)
{
  /* to represent the po aligned in the dot */
  std::map<unsigned,std::set<unsigned> > same_po;
  unsigned max_thread = 0;
  unsigned colour = 0;

  /* to represent the files as clusters */
  std::map<irep_idt,std::set<unsigned> > same_file;

  for(std::set<event_grapht::critical_cyclet>::const_iterator it =
    set.begin(); it!=set.end(); it++)
  {
#ifdef PRINT_UNSAFES
    std::cout << it->print_unsafes() << std::endl;
#endif
    it->print_dot(dot,colour++,model);
    ref << it->print_name(model) << std::endl;
    output << it->print_output() << std::endl;

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
      dot << "subgraph cluster_" << it->first.hash() << "{" << std::endl;
      dot << "  label=\"" << it->first << "\";" << std::endl;
      for(std::set<unsigned>::const_iterator ev_it=it->second.begin();
        ev_it!=it->second.end(); ev_it++)
      {
        dot << "  " << egraph[*ev_it].id << ";" << std::endl;
      }
      dot << "};" << std::endl;
    }
}

void instrumentert::print_outputs(weak_memory_modelt model)
{
  std::ofstream dot;
  std::ofstream ref;
  std::ofstream output;

  dot.open("cycles.dot");
  ref.open("ref.txt");
  output.open("output.txt");

  dot << "digraph G {" << std::endl;
  dot << "nodesep=1; ranksep=1;" << std::endl;

  /* prints cycles in the different outputs */
  if(!set_of_cycles.empty())
    print_outputs_local(set_of_cycles,dot,ref,output,model);
  else if(num_sccs!=0)
  {
    for(unsigned i=0; i<num_sccs; i++)
    {
      std::ofstream local_dot;
      std::string name = "scc_" + i2string(i) + ".dot";
      local_dot.open(name.c_str());

      local_dot << "digraph G {" << std::endl;
      local_dot << "nodesep=1; ranksep=1;" << std::endl;
      print_outputs_local(set_of_cycles_per_SCC[i],local_dot,ref,output,model);
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
}

/*******************************************************************\

Function: instrumentert::collect_cycles_by_SCCs
  
  Inputs:
  
 Outputs:
  
 Purpose: Note: can be distributed (#define DISTRIBUTED)
  
\*******************************************************************/

#ifndef DISTRIBUTED
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
