/*******************************************************************\

Module: Turns a goto-program into an abstract event graph

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

/// \file
/// Turns a goto-program into an abstract event graph

#include "goto2graph.h"

#include <vector>
#include <string>
#include <fstream>

#include <util/options.h>

#include <linking/static_lifetime_init.h>

#include <goto-instrument/rw_set.h>

#include "fence.h"

// #define PRINT_UNSAFES


/// is local variable?
bool inline instrumentert::local(const irep_idt &id)
{
  std::string identifier=id2string(id);

  if(has_prefix(identifier, "symex_invalid") ||
     has_prefix(identifier, "symex::invalid"))
  {
    /* symex_invalid and symex::invalid_object generated when pointer analysis
       fails */
    return true;
  }

  if(identifier==CPROVER_PREFIX "alloc" ||
    identifier==CPROVER_PREFIX "alloc_size" ||
    identifier=="stdin" ||
    identifier=="stdout" ||
    identifier=="stderr" ||
    identifier=="sys_nerr" ||
    has_prefix(identifier, "__unbuffered_"))
    return true;

  const size_t pos=identifier.find("[]");

  if(pos!=std::string::npos)
  {
    /* we don't distinguish the members of an array for the moment */
    identifier.erase(pos);
  }

  try
  {
    const symbolt &symbol=ns.lookup(identifier);

    if(!symbol.is_static_lifetime)
      return true; /* these are local */

    if(symbol.is_thread_local)
      return true; /* these are local */

    return false;
  }
  catch(const std::string &exception)
  {
    message.debug()<<"Exception: "<<exception << messaget::eom;
    return false;
  }
}

bool inline instrumentert::cfg_visitort::local(const irep_idt &i)
{
  return instrumenter.local(i);
}

/// goes through CFG and build a static abstract event graph overapproximating
/// the read/write relations for any executions
unsigned instrumentert::goto2graph_cfg(
  value_setst &value_sets,
  memory_modelt model,
  bool no_dependencies,
  loop_strategyt duplicate_body)
{
  if(!no_dependencies)
    message.status() << "Dependencies analysis enabled" << messaget::eom;

  /* builds the graph following the CFG */
  cfg_visitort visitor(ns, *this);
  visitor.visit_cfg(value_sets, model, no_dependencies, duplicate_body,
    goto_functions.entry_point());

  std::vector<std::size_t> subgraph_index;
  num_sccs=egraph_alt.SCCs(subgraph_index);
  assert(egraph_SCCs.empty());
  egraph_SCCs.resize(num_sccs, std::set<event_idt>());
  for(std::map<event_idt, event_idt>::const_iterator
      it=map_vertex_gnode.begin();
      it!=map_vertex_gnode.end();
      it++)
  {
    const std::size_t sg=subgraph_index[it->second];
    egraph_SCCs[sg].insert(it->first);
  }

  message.status() << "Number of threads detected: "
                   << visitor.max_thread << messaget::eom;

  /* SCCs which could host critical cycles */
  unsigned interesting_sccs=0;
  for(unsigned i=0; i<num_sccs; i++)
    if(egraph_SCCs[i].size()>3)
      interesting_sccs++;

  message.statistics() << "Graph with " << egraph_alt.size() << " nodes has "
                       << interesting_sccs << " interesting SCCs"
                       << messaget::eom;

  message.statistics() << "Number of reads: " << visitor.read_counter
                       << messaget::eom;
  message.statistics() << "Number of writes: " << visitor.write_counter
                       << messaget::eom;
  message.statistics() << "Number of wse: " << visitor.ws_counter
                       << messaget::eom;
  message.statistics() << "Number of rfe/fre: " << visitor.fr_rf_counter
                       << messaget::eom;
  std::size_t instr_counter=0;
  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      ++it)
    instr_counter+=it->second.body.instructions.size();
  message.statistics() << "Number of goto-instructions: "
                       << instr_counter<<messaget::eom;

  return visitor.max_thread;
}

void instrumentert::cfg_visitort::visit_cfg_function(
  value_setst &value_sets,
  memory_modelt model,
  bool no_dependencies,
  loop_strategyt replicate_body,
  const irep_idt &function_id,
  std::set<instrumentert::cfg_visitort::nodet> &ending_vertex)
{
  /* flow: egraph */

  instrumenter.message.debug()
    << "visit function " << function_id << messaget::eom;

  if(function_id == INITIALIZE_FUNCTION)
  {
    return;
  }

#ifdef LOCAL_MAY
  local_may_aliast local_may(
    instrumenter.goto_functions.function_map[function_id]);
#endif

  /* goes through the function */
  goto_programt &goto_program =
    instrumenter.goto_functions.function_map[function_id].body;
  Forall_goto_program_instructions(i_it, goto_program)
  {
    goto_programt::instructiont &instruction=*i_it;

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

    instrumenter.message.debug() << "visit instruction "<<instruction.type
      << messaget::eom;

    if(instruction.is_start_thread() || instruction.is_end_thread())
    {
      /* break the flow */
      visit_cfg_thread();
    }
    else if(instruction.is_atomic_begin() || instruction.is_atomic_end())
    {
      /* break the flow (def 1) or add full barrier (def 2) */
      #ifdef ATOMIC_BREAK
      visit_cfg_thread();
      #elif defined ATOMIC_FENCE
      visit_cfg_fence(i_it);
      #else
      /* propagates */
      visit_cfg_propagate(i_it);
      #endif
    }
    /* a:=b -o-> Rb -po-> Wa */
    else if(instruction.is_assign())
    {
      visit_cfg_assign(
        value_sets,
        function_id,
        i_it,
        no_dependencies
#ifdef LOCAL_MAY
        ,
        local_may
#endif
      ); // NOLINT(whitespace/parens)
    }
    else if(is_fence(instruction, instrumenter.ns))
    {
      instrumenter.message.debug() << "Constructing a fence" << messaget::eom;
      visit_cfg_fence(i_it);
    }
    else if(model!=TSO && is_lwfence(instruction, instrumenter.ns))
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
      visit_cfg_function_call(value_sets, i_it, model,
        no_dependencies, replicate_body);
    }
    else if(instruction.is_goto())
    {
      visit_cfg_goto(
        function_id,
        goto_program,
        i_it,
        replicate_body,
        value_sets
#ifdef LOCAL_MAY
        ,
        local_may
#endif
      ); // NOLINT(whitespace/parens)
    }
#ifdef CONTEXT_INSENSITIVE
    else if(instruction.is_return())
    {
      visit_cfg_propagate(i_it);
      add_all_pos(it, out_nodes[function_id], in_pos[i_it]);
    }
#endif
    else
    {
      /* propagates */
      visit_cfg_propagate(i_it);
    }
  }

  std::pair<unsigned, data_dpt> new_dp(thread, data_dp);
  egraph.map_data_dp.insert(new_dp);
  data_dp.print(instrumenter.message);

  if(instrumenter.goto_functions.function_map[function_id]
       .body.instructions.empty())
  {
    /* empty set of ending edges */
  }
  else
  {
    goto_programt::instructionst::iterator it =
      instrumenter.goto_functions.function_map[function_id]
        .body.instructions.end();
    --it;
    ending_vertex=in_pos[it];
  }
}

void inline instrumentert::cfg_visitort::visit_cfg_propagate(
  goto_programt::instructionst::iterator i_it)
{
  const goto_programt::instructiont &instruction=*i_it;
  /* propagation */
  in_pos[i_it].clear();
  for(const auto &in : instruction.incoming_edges)
    if(in_pos.find(in)!=in_pos.end())
      for(const auto &node : in_pos[in])
        in_pos[i_it].insert(node);
}

void instrumentert::cfg_visitort::visit_cfg_thread() const
{
}

/// references the first and last edges of the function
/* OBSOLETE */
/* Note: can be merged with visit_cfg_body */
/* Warning: we iterate here over the successive instructions of the
   regardless of the gotos. This function has to be called *AFTER*
   an exploration of the function constructing the graph. */
void inline instrumentert::cfg_visitort::visit_cfg_reference_function(
  irep_idt id_function)
{
  if(instrumenter.map_function_graph.find(id_function)!=
     instrumenter.map_function_graph.end())
    return;

  /* gets the body of the function */
  goto_programt::instructionst &body=instrumenter.goto_functions
    .function_map[id_function].body.instructions;

  if(body.empty())
    return;

  /* end of function */
  /* TODO: ensure that all the returns point to the last statement if the
     function, or alternatively make i_it point to each return location in
     the function */
  goto_programt::instructionst::iterator i_it=body.end();
  --i_it;

  /* beginning of the function */
  goto_programt::instructionst::iterator targ=body.begin();

  std::set<event_idt> in_nodes;
  std::set<event_idt> out_nodes;

  /* if the target has already been covered by fwd analysis */
  if(in_pos.find(targ)!=in_pos.end())
  {
    /* if in_pos was updated at this program point */
    if(updated.find(targ)!=updated.end())
    {
      /* connects the previous nodes to those ones */
      for(std::set<nodet>::const_iterator to=in_pos[targ].begin();
          to!=in_pos[targ].end(); ++to)
        in_nodes.insert(to->first);
      for(std::set<nodet>::const_iterator from=in_pos[i_it].begin();
          from!=in_pos[i_it].end(); ++from)
        out_nodes.insert(from->first);
    }
    else
    {
      instrumenter.message.debug() << "else case" << messaget::eom;
      /* connects NEXT nodes following the targets -- bwd analysis */
      for(goto_programt::instructionst::iterator cur=i_it;
          cur!=targ; --cur)
      {
        instrumenter.message.debug() << "i" << messaget::eom;
        for(const auto &in : cur->incoming_edges)
        {
          instrumenter.message.debug() << "t" << messaget::eom;
          if(in_pos.find(in)!=in_pos.end() &&
             updated.find(in)!=updated.end())
          {
            /* out_pos[in].insert(in_pos[in])*/
            add_all_pos(it1, out_pos[in], in_pos[in]);
          }
          else if(in_pos.find(in)!=in_pos.end())
          {
            /* out_pos[in].insert(out_pos[cur])*/
            add_all_pos(it2, out_pos[in], out_pos[cur]);
          }
        }
      }

      /* connects the previous nodes to those ones */
      if(out_pos.find(targ)!=out_pos.end())
      {
        for(std::set<nodet>::const_iterator to=out_pos[targ].begin();
            to!=out_pos[targ].end(); ++to)
          in_nodes.insert(to->first);
        for(std::set<nodet>::const_iterator from=in_pos[i_it].begin();
            from!=in_pos[i_it].end(); ++from)
          out_nodes.insert(from->first);
      }
    }
  }

  instrumenter.map_function_graph[id_function]=
    std::make_pair(in_nodes, out_nodes);
}

event_idt alt_copy_segment(wmm_grapht &alt_egraph,
  event_idt begin, event_idt end)
{
  /* no need to duplicate the loop nodes for the SCC-detection graph -- a
     single back-edge will ensure the same connectivity */
  alt_egraph.add_edge(end, begin);
  return end;
}

bool instrumentert::cfg_visitort::contains_shared_array(
  const irep_idt &function_id,
  goto_programt::const_targett targ,
  goto_programt::const_targett i_it,
  value_setst &value_sets
#ifdef LOCAL_MAY
  ,
  local_may_aliast local_may
#endif
  ) const // NOLINT(whitespace/parens)
{
  instrumenter.message.debug() << "contains_shared_array called for "
    << targ->source_location.get_line() << " and "
    << i_it->source_location.get_line() << messaget::eom;
  for(goto_programt::const_targett cur=targ; cur!=i_it; ++cur)
  {
    instrumenter.message.debug() << "Do we have an array at line "
      <<cur->source_location.get_line()<<"?" << messaget::eom;
    rw_set_loct rw_set(
      ns,
      value_sets,
      function_id,
      cur
#ifdef LOCAL_MAY
      ,
      local_may
#endif
    ); // NOLINT(whitespace/parens)
    instrumenter.message.debug() << "Writes: "<<rw_set.w_entries.size()
      <<"; Reads:"<<rw_set.r_entries.size() << messaget::eom;

    forall_rw_set_r_entries(r_it, rw_set)
    {
      const irep_idt var=r_it->second.object;
      instrumenter.message.debug() << "Is "<<var<<" an array?"
        << messaget::eom;
      if(id2string(var).find("[]")!=std::string::npos
        && !instrumenter.local(var))
        return true;
    }

    forall_rw_set_w_entries(w_it, rw_set)
    {
      const irep_idt var=w_it->second.object;
      instrumenter.message.debug()<<"Is "<<var<<" an array?"<<messaget::eom;
      if(id2string(var).find("[]")!=std::string::npos
        && !instrumenter.local(var))
        return true;
    }
  }

  return false;
}


/// strategy: fwd/bwd alternation
void inline instrumentert::cfg_visitort::visit_cfg_body(
  const irep_idt &function_id,
  const goto_programt &goto_program,
  goto_programt::const_targett i_it,
  loop_strategyt replicate_body,
  value_setst &value_sets
#ifdef LOCAL_MAY
  ,
  local_may_aliast &local_may
#endif
)
{
  /* for each target of the goto */
  for(const auto &target : i_it->targets)
  {
    /* if the target has already been covered by fwd analysis */
    if(in_pos.find(target)!=in_pos.end())
    {
      if(in_pos[i_it].empty())
        continue;

      bool duplicate_this=false;

      switch(replicate_body)
      {
        case arrays_only:
          duplicate_this = contains_shared_array(
            function_id,
            target,
            i_it,
            value_sets
#ifdef LOCAL_MAY
            ,
            local_may
#endif
          ); // NOLINT(whitespace/parens)
          break;
        case all_loops:
          duplicate_this=true;
          break;
        case no_loop:
          duplicate_this=false;
          break;
      }

      if(duplicate_this)
        visit_cfg_duplicate(goto_program, target, i_it);
      else
        visit_cfg_backedge(target, i_it);
    }
  }
}

void inline instrumentert::cfg_visitort::visit_cfg_duplicate(
  const goto_programt &goto_program,
  goto_programt::const_targett targ,
  goto_programt::const_targett i_it)
{
  instrumenter.message.status() << "Duplication..." << messaget::eom;

  bool found_pos=false;
  goto_programt::const_targett new_targ=targ;

  if(in_pos[targ].empty())
  {
    /* tries to find the next node after the back edge */
    for(; new_targ != goto_program.instructions.end(); ++new_targ)
    {
      if(in_pos.find(new_targ)!=in_pos.end() && !in_pos[new_targ].empty())
      {
        found_pos=true;
        break;
      }
    }

    if(!found_pos
      || new_targ->source_location.get_function()
        !=targ->source_location.get_function()
      || new_targ->source_location.get_file()
        !=targ->source_location.get_file())
      return;
  }

  /* appends the body once more */
  const std::set<nodet> &up_set=in_pos[(found_pos ? new_targ : targ)];
  const std::set<nodet> &down_set=in_pos[i_it];

  for(std::set<nodet>::const_iterator begin_it=up_set.begin();
    begin_it!=up_set.end(); ++begin_it)
    instrumenter.message.debug() << "Up " << begin_it->first << messaget::eom;

  for(std::set<nodet>::const_iterator begin_it=down_set.begin();
    begin_it!=down_set.end(); ++begin_it)
    instrumenter.message.debug() << "Down " << begin_it->first <<messaget::eom;

  for(std::set<nodet>::const_iterator begin_it=up_set.begin();
    begin_it!=up_set.end(); ++begin_it)
  {
    for(std::set<nodet>::const_iterator end_it=down_set.begin();
      end_it!=down_set.end(); ++end_it)
    {
      egraph.copy_segment(begin_it->first, end_it->first);
      alt_copy_segment(egraph_alt, begin_it->second, end_it->second);
#if 0
      const event_idt end=egraph.copy_segment(begin_it->first, end_it->first);
      const event_idt alt_end=
        alt_copy_segment(egraph_alt, begin_it->second, end_it->second);
      // copied; no need for back-edge!
      // in_pos[i_it].insert(nodet(end, alt_end));
#endif
    }
  }
}

/// strategy: fwd/bwd alternation
void inline instrumentert::cfg_visitort::visit_cfg_backedge(
  goto_programt::const_targett targ,
  goto_programt::const_targett i_it)
{
  /* if in_pos was updated at this program point */
  if(updated.find(targ)!=updated.end())
  {
    /* connects the previous nodes to those ones */
    for(std::set<nodet>::const_iterator to=in_pos[targ].begin();
      to!=in_pos[targ].end(); ++to)
      for(std::set<nodet>::const_iterator from=in_pos[i_it].begin();
        from!=in_pos[i_it].end(); ++from)
        if(from->first!=to->first)
        {
          if(egraph[from->first].thread!=egraph[to->first].thread)
             continue;
          instrumenter.message.debug() << from->first << "-po->"
                                       << to->first << messaget::eom;
          egraph.add_po_back_edge(from->first, to->first);
          egraph_alt.add_edge(from->second, to->second);
        }
  }
  else
  {
    instrumenter.message.debug() << "else case" << messaget::eom;

    /* connects NEXT nodes following the targets -- bwd analysis */
    for(goto_programt::const_targett cur=i_it;
        cur!=targ; --cur)
    {
      for(const auto &in : cur->incoming_edges)
      {
        if(in_pos.find(in)!=in_pos.end()
          && updated.find(in)!=updated.end())
        {
          /* out_pos[in].insert(in_pos[in])*/
          add_all_pos(it1, out_pos[in], in_pos[in]);
        }
        else if(in_pos.find(in)!=in_pos.end())
        {
          /* out_pos[in].insert(in_pos[cur])*/
          add_all_pos(it2, out_pos[in], out_pos[cur]);
        }
      }
    }

    /* connects the previous nodes to those ones */
    if(out_pos.find(targ)!=out_pos.end())
    {
      for(std::set<nodet>::const_iterator to=out_pos[targ].begin();
          to!=out_pos[targ].end(); ++to)
        for(std::set<nodet>::const_iterator from=in_pos[i_it].begin();
            from!=in_pos[i_it].end(); ++from)
          if(from->first!=to->first)
          {
            if(egraph[from->first].thread!=egraph[to->first].thread)
              continue;
            instrumenter.message.debug() << from->first<<"-po->"
              <<to->first << messaget::eom;
            egraph.add_po_back_edge(from->first, to->first);
            egraph_alt.add_edge(from->second, to->second);
          }
    }
  }
}

void instrumentert::cfg_visitort::visit_cfg_goto(
  const irep_idt &function_id,
  const goto_programt &goto_program,
  goto_programt::instructionst::iterator i_it,
  loop_strategyt replicate_body,
  value_setst &value_sets
#ifdef LOCAL_MAY
  ,
  local_may_aliast &local_may
#endif
)
{
  const goto_programt::instructiont &instruction=*i_it;

  /* propagates */
  visit_cfg_propagate(i_it);

  /* if back-edges, constructs them too:
     if goto to event, connects previously propagated events to it;
     if not, we need to find which events AFTER the target are to
     be connected. We do a backward analysis. */
  if(instruction.is_backwards_goto())
  {
    instrumenter.message.debug() << "backward goto" << messaget::eom;
    visit_cfg_body(
      function_id,
      goto_program,
      i_it,
      replicate_body,
      value_sets
#ifdef LOCAL_MAY
      ,
      local_may
#endif
    ); // NOLINT(whitespace/parens)
  }
}

void instrumentert::cfg_visitort::visit_cfg_function_call(
  value_setst &value_sets,
  goto_programt::instructionst::iterator i_it,
  memory_modelt model,
  bool no_dependencies,
  loop_strategyt replicate_body)
{
  const goto_programt::instructiont &instruction=*i_it;

  const exprt &fun=to_code_function_call(instruction.code).function();
  const irep_idt &fun_id=to_symbol_expr(fun).get_identifier();
  /* ignore recursive calls -- underapproximation */
  try
  {
    enter_function(fun_id);
    #ifdef CONTEXT_INSENSITIVE
    stack_fun.push(cur_fun);
    cur_fun=fun_id;
    #endif

    #if 0
    if(!inline_function_cond(fun_id))
    {
      /* do not inline it, connect to an existing subgraph or create a new
         one */
      if(instrumenter.map_function_graph.find(fun_id)!=
         instrumenter.map_function_graph.end())
      {
        /* connects to existing */
        /* TODO */
      }
      else
      {
        /* just inlines */
        /* TODO */
        visit_cfg_function(value_sets, model, no_dependencies, fun_id,
          in_pos[i_it]);
        updated.insert(i_it);
      }
    }
    else // NOLINT(readability/braces)
    #endif
    {
      /* normal inlining strategy */
      visit_cfg_function(value_sets, model, no_dependencies, replicate_body,
        fun_id, in_pos[i_it]);
      updated.insert(i_it);
    }

    leave_function(fun_id);
    #ifdef CONTEXT_INSENSITIVE
    cur_fun=stack_fun.pop();
    #endif
  }
  catch(const std::string &s)
  {
    instrumenter.message.warning() << "sorry, doesn't handle recursion "
                                   << "(function " << fun_id << "; .cpp) "
                                   << s << messaget::eom;
  }
}

void instrumentert::cfg_visitort::visit_cfg_lwfence(
  goto_programt::instructionst::iterator i_it)
{
  const goto_programt::instructiont &instruction=*i_it;
  const abstract_eventt new_fence_event(abstract_eventt::operationt::Lwfence,
    thread, "f", instrumenter.unique_id++, instruction.source_location, false);
  const event_idt new_fence_node=egraph.add_node();
  egraph[new_fence_node](new_fence_event);
  const event_idt new_fence_gnode=egraph_alt.add_node();
  egraph_alt[new_fence_gnode]=new_fence_event;
  instrumenter.map_vertex_gnode.insert(
    std::make_pair(new_fence_node, new_fence_gnode));

  for(const auto &in : instruction.incoming_edges)
    if(in_pos.find(in)!=in_pos.end())
    {
      for(const auto &node : in_pos[in])
      {
        if(egraph[node.first].thread!=thread)
             continue;
        instrumenter.message.debug() << node.first<<"-po->"<<new_fence_node
          << messaget::eom;
        egraph.add_po_edge(node.first, new_fence_node);
        egraph_alt.add_edge(node.second, new_fence_gnode);
      }
    }

  in_pos[i_it].clear();
  in_pos[i_it].insert(nodet(new_fence_node, new_fence_gnode));
  updated.insert(i_it);
}

void instrumentert::cfg_visitort::visit_cfg_asm_fence(
  goto_programt::instructionst::iterator i_it)
{
  const goto_programt::instructiont &instruction=*i_it;
  bool WRfence=instruction.code.get_bool(ID_WRfence);
  bool WWfence=instruction.code.get_bool(ID_WWfence);
  bool RRfence=instruction.code.get_bool(ID_RRfence);
  bool RWfence=instruction.code.get_bool(ID_RWfence);
  bool WWcumul=instruction.code.get_bool(ID_WWcumul);
  bool RRcumul=instruction.code.get_bool(ID_RRcumul);
  bool RWcumul=instruction.code.get_bool(ID_RWcumul);
  const abstract_eventt new_fence_event(abstract_eventt::operationt::ASMfence,
    thread, "asm", instrumenter.unique_id++, instruction.source_location,
    false, WRfence, WWfence, RRfence, RWfence, WWcumul, RWcumul, RRcumul);
  const event_idt new_fence_node=egraph.add_node();
  egraph[new_fence_node](new_fence_event);
  const event_idt new_fence_gnode=egraph_alt.add_node();
  egraph_alt[new_fence_gnode]=new_fence_event;
  instrumenter.map_vertex_gnode.insert(
    std::make_pair(new_fence_node, new_fence_gnode));

  for(const auto &in : instruction.incoming_edges)
    if(in_pos.find(in)!=in_pos.end())
    {
      for(const auto &node : in_pos[in])
      {
        if(egraph[node.first].thread!=thread)
           continue;
        instrumenter.message.debug() << node.first<<"-po->"<<new_fence_node
          << messaget::eom;
        egraph.add_po_edge(node.first, new_fence_node);
        egraph_alt.add_edge(node.second, new_fence_gnode);
      }
    }

  in_pos[i_it].clear();
  in_pos[i_it].insert(nodet(new_fence_node, new_fence_gnode));
  updated.insert(i_it);
}

void instrumentert::cfg_visitort::visit_cfg_assign(
  value_setst &value_sets,
  const irep_idt &function_id,
  goto_programt::instructionst::iterator &i_it,
  bool no_dependencies
#ifdef LOCAL_MAY
  ,
  local_may_aliast &local_may
#endif
)
{
  goto_programt::instructiont &instruction=*i_it;

  /* Read (Rb) */
  rw_set_loct rw_set(
    ns,
    value_sets,
    function_id,
    i_it
#ifdef LOCAL_MAY
    ,
    local_may
#endif
  ); // NOLINT(whitespace/parens)

  event_idt previous=std::numeric_limits<event_idt>::max();
  event_idt previous_gnode=std::numeric_limits<event_idt>::max();

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
    const irep_idt &read=r_it->second.object;

    /* skip local variables */
    if(local(read))
      continue;

    read_counter++;
#if 0
    assert(read_expr);
#endif

    const abstract_eventt new_read_event(abstract_eventt::operationt::Read,
      thread, id2string(read), instrumenter.unique_id++,
      instruction.source_location, local(read));

    const event_idt new_read_node=egraph.add_node();
    egraph[new_read_node]=new_read_event;
    instrumenter.message.debug() << "new Read"<<read<<" @thread"
      <<(thread)<<"("<<instruction.source_location<<","
      <<(local(read)?"local":"shared")<<") #"<<new_read_node
      << messaget::eom;

    if(read==ID_unknown)
      unknown_read_nodes.insert(new_read_node);

    const event_idt new_read_gnode=egraph_alt.add_node();
    egraph_alt[new_read_gnode]=new_read_event;
    instrumenter.map_vertex_gnode.insert(
    std::make_pair(new_read_node, new_read_gnode));

    /* creates ... -po-> Read */
    for(const auto &in : instruction.incoming_edges)
    {
      if(in_pos.find(in)!=in_pos.end())
      {
        for(const auto &node : in_pos[in])
        {
           if(egraph[node.first].thread!=thread)
             continue;
           instrumenter.message.debug() << node.first<<"-po->"
             <<new_read_node << messaget::eom;
           egraph.add_po_edge(node.first, new_read_node);
           egraph_alt.add_edge(node.second, new_read_gnode);
        }
      }
    }

    map_reads.insert(id2node_pairt(read, new_read_node));
    previous=new_read_node;
    previous_gnode=new_read_gnode;

    /* creates Read <-com-> Write ... */
    const std::pair<id2nodet::iterator, id2nodet::iterator>
      with_same_var=map_writes.equal_range(read);
    for(id2nodet::iterator id_it=with_same_var.first;
      id_it!=with_same_var.second; id_it++)
      if(egraph[id_it->second].thread!=new_read_event.thread)
      {
        instrumenter.message.debug() << id_it->second<<"<-com->"
          <<new_read_node << messaget::eom;
        std::map<event_idt, event_idt>::const_iterator entry=
          instrumenter.map_vertex_gnode.find(id_it->second);
        assert(entry!=instrumenter.map_vertex_gnode.end());
        egraph.add_com_edge(new_read_node, id_it->second);
        egraph_alt.add_edge(new_read_gnode, entry->second);
        egraph.add_com_edge(id_it->second, new_read_node);
        egraph_alt.add_edge(entry->second, new_read_gnode);
        ++fr_rf_counter;
      }

    /* for unknown writes */
    for(std::set<event_idt>::const_iterator id_it=
      unknown_write_nodes.begin();
      id_it!=unknown_write_nodes.end();
      ++id_it)
      if(egraph[*id_it].thread!=new_read_event.thread)
      {
        instrumenter.message.debug() << *id_it<<"<-com->"
          <<new_read_node << messaget::eom;
        std::map<event_idt, event_idt>::const_iterator entry=
          instrumenter.map_vertex_gnode.find(*id_it);
        assert(entry!=instrumenter.map_vertex_gnode.end());
        egraph.add_com_edge(new_read_node, *id_it);
        egraph_alt.add_edge(new_read_gnode, entry->second);
        egraph.add_com_edge(*id_it, new_read_node);
        egraph_alt.add_edge(entry->second, new_read_gnode);
        ++fr_rf_counter;
      }
  }

  /* Write (Wa) */
  forall_rw_set_w_entries(w_it, rw_set)
  {
    /* creates Write:
       write is the irep_id in the code;
       new_write_event is the corresponding abstract event;
       new_write_node is the node in the graph */
    const irep_idt &write=w_it->second.object;

    instrumenter.message.debug() << "WRITE: " << write << messaget::eom;

    /* skip local variables */
    if(local(write))
      continue;

    ++write_counter;
    // assert(write_expr);

    /* creates Write */
    const abstract_eventt new_write_event(abstract_eventt::operationt::Write,
      thread, id2string(write), instrumenter.unique_id++,
      instruction.source_location, local(write));

    const event_idt new_write_node=egraph.add_node();
    egraph[new_write_node](new_write_event);
    instrumenter.message.debug() << "new Write "<<write<<" @thread"<<(thread)
      <<"("<<instruction.source_location<<","
      << (local(write)?"local":"shared")<<") #"<<new_write_node
      << messaget::eom;

    if(write==ID_unknown)
      unknown_read_nodes.insert(new_write_node);

    const event_idt new_write_gnode=egraph_alt.add_node();
    egraph_alt[new_write_gnode]=new_write_event;
    instrumenter.map_vertex_gnode.insert(
      std::pair<event_idt, event_idt>(new_write_node, new_write_gnode));

    /* creates Read -po-> Write */
    if(previous!=std::numeric_limits<event_idt>::max())
    {
      instrumenter.message.debug() << previous<<"-po->"<<new_write_node
        << messaget::eom;
      egraph.add_po_edge(previous, new_write_node);
      egraph_alt.add_edge(previous_gnode, new_write_gnode);
    }
    else
    {
      for(const auto &in : instruction.incoming_edges)
      {
        if(in_pos.find(in)!=in_pos.end())
        {
          for(const auto &node : in_pos[in])
          {
            if(egraph[node.first].thread!=thread)
              continue;
            instrumenter.message.debug() << node.first<<"-po->"
              <<new_write_node << messaget::eom;
            egraph.add_po_edge(node.first, new_write_node);
            egraph_alt.add_edge(node.second, new_write_gnode);
          }
        }
      }
    }

    /* creates Write <-com-> Read */
    const std::pair<id2nodet::iterator, id2nodet::iterator>
      r_with_same_var=map_reads.equal_range(write);
    for(id2nodet::iterator idr_it=r_with_same_var.first;
        idr_it!=r_with_same_var.second; idr_it++)
      if(egraph[idr_it->second].thread!=new_write_event.thread)
      {
        instrumenter.message.debug() <<idr_it->second<<"<-com->"
          <<new_write_node << messaget::eom;
        std::map<event_idt, event_idt>::const_iterator entry=
          instrumenter.map_vertex_gnode.find(idr_it->second);
        assert(entry!=instrumenter.map_vertex_gnode.end());
        egraph.add_com_edge(new_write_node, idr_it->second);
        egraph_alt.add_edge(new_write_gnode, entry->second);
        egraph.add_com_edge(idr_it->second, new_write_node);
        egraph_alt.add_edge(entry->second, new_write_gnode);
        ++fr_rf_counter;
      }

    /* creates Write <-com-> Write */
    const std::pair<id2nodet::iterator, id2nodet::iterator>
      w_with_same_var=map_writes.equal_range(write);
    for(id2nodet::iterator idw_it=w_with_same_var.first;
        idw_it!=w_with_same_var.second; idw_it++)
      if(egraph[idw_it->second].thread!=new_write_event.thread)
      {
        instrumenter.message.debug() << idw_it->second<<"<-com->"
          <<new_write_node << messaget::eom;
        std::map<event_idt, event_idt>::const_iterator entry=
          instrumenter.map_vertex_gnode.find(idw_it->second);
        assert(entry!=instrumenter.map_vertex_gnode.end());
        egraph.add_com_edge(new_write_node, idw_it->second);
        egraph_alt.add_edge(new_write_gnode, entry->second);
        egraph.add_com_edge(idw_it->second, new_write_node);
        egraph_alt.add_edge(entry->second, new_write_gnode);
        ++ws_counter;
      }

    /* for unknown writes */
    for(std::set<event_idt>::const_iterator id_it=
        unknown_write_nodes.begin();
        id_it!=unknown_write_nodes.end();
        ++id_it)
      if(egraph[*id_it].thread!=new_write_event.thread)
      {
        instrumenter.message.debug() << *id_it<<"<-com->"
          <<new_write_node << messaget::eom;
        std::map<event_idt, event_idt>::const_iterator entry=
          instrumenter.map_vertex_gnode.find(*id_it);
        assert(entry!=instrumenter.map_vertex_gnode.end());
        egraph.add_com_edge(new_write_node, *id_it);
        egraph_alt.add_edge(new_write_gnode, entry->second);
        egraph.add_com_edge(*id_it, new_write_node);
        egraph_alt.add_edge(entry->second, new_write_gnode);
        ++fr_rf_counter;
      }

    /* for unknown reads */
    for(std::set<event_idt>::const_iterator id_it=
        unknown_read_nodes.begin();
        id_it!=unknown_read_nodes.end();
        ++id_it)
      if(egraph[*id_it].thread!=new_write_event.thread)
      {
        instrumenter.message.debug() << *id_it<<"<-com->"
          <<new_write_node << messaget::eom;
        std::map<event_idt, event_idt>::const_iterator entry=
          instrumenter.map_vertex_gnode.find(*id_it);
        assert(entry!=instrumenter.map_vertex_gnode.end());
        egraph.add_com_edge(new_write_node, *id_it);
        egraph_alt.add_edge(new_write_gnode, entry->second);
        egraph.add_com_edge(*id_it, new_write_node);
        egraph_alt.add_edge(entry->second, new_write_gnode);
        ++fr_rf_counter;
      }


    map_writes.insert(id2node_pairt(write, new_write_node));
    previous=new_write_node;
    previous_gnode=new_write_gnode;
  }

  if(previous!=std::numeric_limits<event_idt>::max())
  {
    in_pos[i_it].clear();
    in_pos[i_it].insert(nodet(previous, previous_gnode));
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
        const irep_idt &write=write_it->second.object;
        const irep_idt &read=read_it->second.object;
        instrumenter.message.debug() << "dp: Write:"<<write<<"; Read:"<<read
          << messaget::eom;
        const datat read_p(read, instruction.source_location);
        const datat write_p(write, instruction.source_location);
          data_dp.dp_analysis(read_p, local(read), write_p, local(write));
        }
    data_dp.dp_merge();

    forall_rw_set_r_entries(read2_it, rw_set)
      forall_rw_set_r_entries(read_it, rw_set)
      {
        const irep_idt &read2=read2_it->second.object;
        const irep_idt &read=read_it->second.object;
        if(read2==read)
          continue;
        const datat read_p(read, instruction.source_location);
        const datat read2_p(read2, instruction.source_location);
        data_dp.dp_analysis(read_p, local(read), read2_p, local(read2));
      }
    data_dp.dp_merge();
  }
}

void instrumentert::cfg_visitort::visit_cfg_fence(
  goto_programt::instructionst::iterator i_it)
{
  const goto_programt::instructiont &instruction=*i_it;
  const abstract_eventt new_fence_event(abstract_eventt::operationt::Fence,
    thread, "F", instrumenter.unique_id++, instruction.source_location, false);
  const event_idt new_fence_node=egraph.add_node();
  egraph[new_fence_node](new_fence_event);
  const event_idt new_fence_gnode=egraph_alt.add_node();
  egraph_alt[new_fence_gnode]=new_fence_event;
  instrumenter.map_vertex_gnode.insert(
    std::make_pair(new_fence_node, new_fence_gnode));

  for(const auto &in : instruction.incoming_edges)
    if(in_pos.find(in)!=in_pos.end())
    {
      for(const auto &node : in_pos[in])
      {
        instrumenter.message.debug() << node.first<<"-po->"<<new_fence_node
          << messaget::eom;
        egraph.add_po_edge(node.first, new_fence_node);
        egraph_alt.add_edge(node.second, new_fence_gnode);
      }
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

void instrumentert::cfg_visitort::visit_cfg_skip(
  goto_programt::instructionst::iterator i_it)
{
  visit_cfg_propagate(i_it);
}

void inline instrumentert::add_instr_to_interleaving(
  goto_programt::instructionst::iterator it,
  goto_programt &interleaving)
{
  if(it->is_return() ||
     it->is_throw() ||
     it->is_catch() ||
     it->is_skip() ||
     it->is_dead() ||
     it->is_start_thread() ||
     it->is_end_thread())
    return;

  if(it->is_atomic_begin() ||
     it->is_atomic_end())
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
  goto_programt::targett current_instruction=interleaving.add_instruction();
  goto_programt::instructiont new_instruction(*it);
  current_instruction->swap(new_instruction);
}

bool instrumentert::is_cfg_spurious(const event_grapht::critical_cyclet &cyc)
{
  message.debug() << "spurious by CFG? " << messaget::eom;
  goto_programt interleaving;

  for(event_grapht::critical_cyclet::const_iterator e_it=cyc.begin();
    e_it!=cyc.end() && ++e_it!=cyc.end(); ++e_it)
  {
    --e_it;

    const abstract_eventt &current_event=egraph[*e_it];
    const source_locationt &current_location=current_event.source_location;

    /* select relevant thread (po) -- or function contained in this thread */
    goto_programt *current_po=nullptr;
    bool thread_found=false;

    Forall_goto_functions(f_it, goto_functions)
    {
      forall_goto_program_instructions(p_it, f_it->second.body)
        if(p_it->source_location==current_location)
        {
          current_po=&f_it->second.body;
          thread_found=true;
          break;
        }

      if(thread_found)
        break;
    }
    assert(current_po);

    const wmm_grapht::edgest &pos_cur=egraph.po_out(*e_it);
    const wmm_grapht::edgest &pos_next=egraph.po_out(*(++e_it));
    --e_it;

    bool exists_n=false;

    for(wmm_grapht::edgest::const_iterator edge_it=pos_cur.begin();
      edge_it!=pos_cur.end(); edge_it++)
    {
      if(pos_next.find(edge_it->first)!=pos_next.end())
      {
        exists_n=true;
        break;
      }
    }

    /* !exists n, has_po_edge(*e_it,n) /\ has_po_edge(*(++it--),n) */
    if((++e_it)!=cyc.end() || !exists_n)
    {
      --e_it;

      /* add this instruction to the interleaving */
      Forall_goto_program_instructions(i_it, *current_po)
        if(i_it->source_location==current_location)
        {
          /* add all the instructions of this line */
          for(goto_programt::instructionst::iterator same_loc=i_it;
            same_loc!=current_po->instructions.end()
            && same_loc->source_location==i_it->source_location;
            same_loc++)
            add_instr_to_interleaving(same_loc, interleaving);
          break;
        }
    }
    else
    {
      --e_it;

      /* find the portion of the thread to add */
      const abstract_eventt &next_event=egraph[*(++e_it--)];
      const source_locationt &next_location=next_event.source_location;

      bool in_cycle=false;
      Forall_goto_program_instructions(it, *current_po)
      {
        if(it->source_location==current_location)
          in_cycle=true;

        /* do not add the last instruction now -- will be done at
           the next iteration */
        if(it->source_location==next_location)
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
      for(const auto &t : int_it->targets)
      {
        bool target_in_cycle=false;

        forall_goto_program_instructions(targ, interleaving)
          if(targ==t)
          {
            target_in_cycle=true;
            break;
          }

        if(!target_in_cycle)
        {
          int_it->make_assertion(false_exprt());
          break;
        }
      }
    }

  /* now test whether this part of the code can exist */
  goto_functionst::function_mapt map;
  goto_functiont one_interleaving;
  one_interleaving.body.copy_from(interleaving);
  map.insert(std::make_pair(
    goto_functionst::entry_point(),
    std::move(one_interleaving)));

  goto_functionst this_interleaving;
  this_interleaving.function_map=std::move(map);
  optionst no_option;
  null_message_handlert no_message;

  #if 0
  bmct bmc(no_option, symbol_table, no_message);

  bool is_spurious=bmc.run(this_interleaving);

  message.debug() << "CFG:"<<is_spurious << messaget::eom;
  return is_spurious;
  #else

  return false; // conservative for now
  #endif
}

void instrumentert::cfg_cycles_filter()
{
  if(!set_of_cycles.empty())
  {
    for(std::set<event_grapht::critical_cyclet>::iterator
      it=set_of_cycles.begin();
      it!=set_of_cycles.end();
    )
    {
      bool erased=false;
      std::set<event_grapht::critical_cyclet>::iterator next=it;
      ++next;
      if(is_cfg_spurious(*it))
      {
        erased=true;
        set_of_cycles.erase(it);
      }
      it=next;
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
        bool erased=false;
        std::set<event_grapht::critical_cyclet>::iterator next=it;
        ++next;
        if(is_cfg_spurious(*it))
        {
          erased=true;
          set_of_cycles_per_SCC[i].erase(it);
        }
        it=next;
        if(!erased)
          ++it;
      }
  }
  else
    message.status() << "No cycle to filter" << messaget::eom;
}

void inline instrumentert::print_outputs_local(
  const std::set<event_grapht::critical_cyclet> &set,
  std::ofstream &dot,
  std::ofstream &ref,
  std::ofstream &output,
  std::ofstream &all,
  std::ofstream &table,
  memory_modelt model,
  bool hide_internals)
{
  /* to represent the po aligned in the dot */
  std::map<unsigned, std::set<event_idt> > same_po;
  unsigned max_thread=0;
  unsigned colour=0;

  /* to represent the files as clusters */
  std::map<irep_idt, std::set<event_idt> > same_file;

  /* to summarise in a table all the variables */
  std::map<std::string, std::string> map_id2var;
  std::map<std::string, std::string> map_var2id;

  for(std::set<event_grapht::critical_cyclet>::const_iterator it =
    set.begin(); it!=set.end(); it++)
  {
#ifdef PRINT_UNSAFES
    message.debug() << it->print_unsafes() << messaget::eom;
#endif
    it->print_dot(dot, colour++, model);
    ref << it->print_name(model, hide_internals) << '\n';
    output << it->print_output() << '\n';
    all << it->print_all(model, map_id2var, map_var2id, hide_internals)
      << '\n';

    /* emphasises instrumented events */
    for(std::list<event_idt>::const_iterator it_e=it->begin();
      it_e!=it->end(); it_e++)
    {
      const abstract_eventt &ev=egraph[*it_e];

      if(render_po_aligned)
        same_po[ev.thread].insert(*it_e);
      if(render_by_function)
        same_file[ev.source_location.get_function()].insert(*it_e);
      else if(render_by_file)
        same_file[ev.source_location.get_file()].insert(*it_e);
      if(ev.thread>max_thread)
        max_thread=ev.thread;

      if(var_to_instr.find(ev.variable)!=var_to_instr.end()
        && id2loc.find(ev.variable)!=id2loc.end())
      {
        dot << ev.id << "[label=\"\\\\lb {" << ev.id << "}";
        dot << ev.get_operation() << "{" << ev.variable << "} {} @thread";
        dot << ev.thread << "\",color=red,shape=box];\n";
      }
    }
  }

  /* aligns events by po */
  if(render_po_aligned)
  {
    for(unsigned i=0; i<=max_thread; i++)
      if(!same_po[i].empty())
      {
        dot << "{rank=same; thread_" << i
          << "[shape=plaintext, label=\"thread " << i << "\"];";
        for(std::set<event_idt>::iterator it=same_po[i].begin();
          it!=same_po[i].end(); it++)
          dot << egraph[*it].id << ";";
        dot << "};\n";
      }
  }

  /* clusters events by file/function */
  if(render_by_file || render_by_function)
  {
    for(std::map<irep_idt, std::set<event_idt> >::const_iterator it=
      same_file.begin();
      it!=same_file.end(); it++)
    {
      dot << "subgraph cluster_" << irep_id_hash()(it->first) << "{\n";
      dot << "  label=\"" << it->first << "\";\n";
      for(std::set<event_idt>::const_iterator ev_it=it->second.begin();
        ev_it!=it->second.end(); ev_it++)
      {
        dot << "  " << egraph[*ev_it].id << ";\n";
      }
      dot << "};\n";
    }
  }

  /* variable table for "all" */
  table << std::string(80, '-');
  for(std::map<std::string, std::string>::const_iterator
      m_it=map_id2var.begin();
      m_it!=map_id2var.end();
      ++m_it)
  {
    table << "\n| " << m_it->first << " : " << m_it->second;
  }
  table << '\n';
  table << std::string(80, '-');
  table << '\n';
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

  dot << "digraph G {\n";
  dot << "nodesep=1; ranksep=1;\n";

  /* prints cycles in the different outputs */
  if(!set_of_cycles.empty())
    print_outputs_local(set_of_cycles, dot, ref, output, all, table,
      model, hide_internals);
  else if(num_sccs!=0)
  {
    for(unsigned i=0; i<num_sccs; i++)
    {
      std::ofstream local_dot;
      std::string name="scc_" + std::to_string(i) + ".dot";
      local_dot.open(name.c_str());

      local_dot << "digraph G {\n";
      local_dot << "nodesep=1; ranksep=1;\n";
      print_outputs_local(set_of_cycles_per_SCC[i], local_dot, ref, output, all,
        table, model, hide_internals);
      local_dot << "}\n";
      local_dot.close();

      dot << i << "[label=\"SCC " << i << "\",link=\"" << "scc_" << i;
      dot << ".svg\"]\n";
    }
  }
  else
    message.debug() << "no cycles to output" << messaget::eom;

  dot << "}\n";

  dot.close();
  ref.close();
  output.close();
  all.close();
  table.close();
}

/// Note: can be distributed (\#define DISTRIBUTED)
#if 1
// #ifdef _WIN32
void instrumentert::collect_cycles_by_SCCs(memory_modelt model)
{
  unsigned scc=0;
  set_of_cycles_per_SCC.resize(num_sccs,
    std::set<event_grapht::critical_cyclet>());
  for(std::vector<std::set<event_idt> >::const_iterator it=egraph_SCCs.begin();
    it!=egraph_SCCs.end(); it++)
    if(it->size()>=4)
      egraph.collect_cycles(set_of_cycles_per_SCC[scc++], model, *it);
}
#else
class pthread_argumentt
{
public:
  instrumentert &instr;
  memory_modelt mem;
  const std::set<event_idt> &filter;
  std::set<event_grapht::critical_cyclet> &cycles;

  pthread_argumentt(instrumentert &_instr,
    memory_modelt _mem,
    const std::set<event_idt> &_filter,
    std::set<event_grapht::critical_cyclet> &_cycles)
    :instr(_instr), mem(_mem), filter(_filter), cycles(_cycles)
  {
  }
};

/* wraper */
void *collect_cycles_in_thread(void *arg)
{
  /* arguments */
  pthread_argumentt *p_arg=reinterpret_cast<pthread_argumentt*>(arg);
  instrumentert &this_instrumenter=p_arg->instr;
  memory_modelt model=p_arg->mem;
  const std::set<event_idt> &filter=p_arg->filter;
  std::set<event_grapht::critical_cyclet> &cycles=p_arg->cycles;

  this_instrumenter.egraph.collect_cycles(cycles, model, filter);

  return NULL;
}

void instrumentert::collect_cycles_by_SCCs(memory_modelt model)
{
  const unsigned number_of_sccs=num_sccs;
  std::set<unsigned> interesting_SCCs;

  unsigned scc=0;
  pthread_t *threads=new pthread_t[num_sccs+1];

  set_of_cycles_per_SCC.resize(num_sccs,
    std::set<event_grapht::critical_cyclet>());

  for(std::vector<std::set<unsigned> >::const_iterator it=egraph_SCCs.begin();
      it!=egraph_SCCs.end(); it++)
    if(it->size()>=4)
    {
      interesting_SCCs.insert(scc);
      pthread_argumentt arg(*this, model, *it, set_of_cycles_per_SCC[scc]);

      int rc=pthread_create(&threads[scc++], NULL,
        collect_cycles_in_thread, &arg);

      message.status()<<(rc!=0?"Failure ":"Success ")
        <<"in creating thread for SCC #"<<scc-1<<messaget::eom;
    }

  for(unsigned i=0; i<number_of_sccs; i++)
    if(interesting_SCCs.find(i)!=interesting_SCCs.end())
    {
      int rc=pthread_join(threads[i], NULL);
      message.status()<<(rc!=0?"Failure ":"Success ")
        <<"in joining thread for SCC #"<<i<<messaget::eom;
    }

  delete[] threads;
}
#endif
