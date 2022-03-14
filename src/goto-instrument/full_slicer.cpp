/*******************************************************************\

Module: Slicing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Slicing

#include "full_slicer.h"
#include "full_slicer_class.h"

#include <util/find_symbols.h>
#include <util/cprover_prefix.h>

#include <goto-programs/adjust_float_expressions.h>
#include <goto-programs/remove_skip.h>

void full_slicert::add_dependencies(
  const cfgt::nodet &node,
  queuet &queue,
  const dependence_grapht &dep_graph,
  const dep_node_to_cfgt &dep_node_to_cfg)
{
  const dependence_grapht::nodet &d_node=
    dep_graph[dep_graph[node.PC].get_node_id()];

  for(dependence_grapht::edgest::const_iterator
      it=d_node.in.begin();
      it!=d_node.in.end();
      ++it)
    add_to_queue(queue, dep_node_to_cfg[it->first], node.PC);
}

void full_slicert::add_function_calls(
  const cfgt::nodet &node,
  queuet &queue,
  const goto_functionst &goto_functions)
{
  goto_functionst::function_mapt::const_iterator f_it =
    goto_functions.function_map.find(node.function_id);
  assert(f_it!=goto_functions.function_map.end());

  assert(!f_it->second.body.instructions.empty());
  goto_programt::const_targett begin_function=
    f_it->second.body.instructions.begin();

  const auto &entry = cfg.get_node(begin_function);
  for(const auto &in_edge : entry.in)
    add_to_queue(queue, in_edge.first, node.PC);
}

void full_slicert::add_decl_dead(
  const cfgt::nodet &node,
  queuet &queue,
  decl_deadt &decl_dead)
{
  if(decl_dead.empty())
    return;

  find_symbols_sett syms;

  node.PC->apply([&syms](const exprt &e) { find_symbols(e, syms); });

  for(find_symbols_sett::const_iterator
      it=syms.begin();
      it!=syms.end();
      ++it)
  {
    decl_deadt::iterator entry=decl_dead.find(*it);
    if(entry==decl_dead.end())
      continue;

    while(!entry->second.empty())
    {
      add_to_queue(queue, entry->second.top(), node.PC);
      entry->second.pop();
    }

    decl_dead.erase(entry);
  }
}

void full_slicert::add_jumps(
  queuet &queue,
  jumpst &jumps,
  const dependence_grapht::post_dominators_mapt &post_dominators)
{
  // Based on:
  // On slicing programs with jump statements
  // Hiralal Agrawal, PLDI'94
  // Figure 7:
  // Slice = the slice obtained using the conventional slicing algorithm;
  // do {
  //   Traverse the postdominator tree using the preorder traversal,
  //   and for each jump statement, J, encountered that is
  //     (i) not in Slice and
  //     (ii) whose nearest postdominator in Slice is different from
  //          the nearest lexical successor in Slice) do {
  //            Add J to Slice;
  //            Add the transitive closure of the dependences of J to Slice;
  //          }
  // } until no new jump statements may be added to Slice;
  // For each goto statement, Goto L, in Slice, if the statement
  // labeled L is not in Slice then associate the label L with its
  // nearest postdominator in Slice;
  // return (Slice);

  for(jumpst::iterator
      it=jumps.begin();
      it!=jumps.end();
      ) // no ++it
  {
    jumpst::iterator next=it;
    ++next;

    const cfgt::nodet &j=cfg[*it];

    // is j in the slice already?
    if(j.node_required)
    {
      jumps.erase(it);
      it=next;
      continue;
    }

    // check nearest lexical successor in slice
    goto_programt::const_targett lex_succ=j.PC;
    for( ; !lex_succ->is_end_function(); ++lex_succ)
    {
      if(cfg.get_node(lex_succ).node_required)
        break;
    }
    if(lex_succ->is_end_function())
    {
      it=next;
      continue;
    }

    const irep_idt &id = j.function_id;
    const cfg_post_dominatorst &pd=post_dominators.at(id);

    const auto &j_PC_node = pd.get_node(j.PC);

    // find the nearest post-dominator in slice
    if(!pd.dominates(lex_succ, j_PC_node))
    {
      add_to_queue(queue, *it, lex_succ);
      jumps.erase(it);
    }
    else
    {
      // check whether the nearest post-dominator is different from
      // lex_succ
      goto_programt::const_targett nearest=lex_succ;
      std::size_t post_dom_size=0;
      for(cfg_dominatorst::target_sett::const_iterator d_it =
            j_PC_node.dominators.begin();
          d_it != j_PC_node.dominators.end();
          ++d_it)
      {
        const auto &node = cfg.get_node(*d_it);
        if(node.node_required)
        {
          const irep_idt &id2 = node.function_id;
          INVARIANT(id==id2,
                    "goto/jump expected to be within a single function");

          const auto &postdom_node = pd.get_node(*d_it);

          if(postdom_node.dominators.size() > post_dom_size)
          {
            nearest=*d_it;
            post_dom_size = postdom_node.dominators.size();
          }
        }
      }
      if(nearest!=lex_succ)
      {
        add_to_queue(queue, *it, nearest);
        jumps.erase(it);
      }
    }

    it=next;
  }
}

void full_slicert::fixedpoint(
  goto_functionst &goto_functions,
  queuet &queue,
  jumpst &jumps,
  decl_deadt &decl_dead,
  const dependence_grapht &dep_graph)
{
  std::vector<cfgt::entryt> dep_node_to_cfg;
  dep_node_to_cfg.reserve(dep_graph.size());

  for(dependence_grapht::node_indext i = 0; i < dep_graph.size(); ++i)
    dep_node_to_cfg.push_back(cfg.get_node_index(dep_graph[i].PC));

  // process queue until empty
  while(!queue.empty())
  {
    while(!queue.empty())
    {
      cfgt::entryt e=queue.top();
      cfgt::nodet &node=cfg[e];
      queue.pop();

      // already done by some earlier iteration?
      if(node.node_required)
        continue;

      // node is required
      node.node_required=true;

      // add data and control dependencies of node
      add_dependencies(node, queue, dep_graph, dep_node_to_cfg);

      // retain all calls of the containing function
      add_function_calls(node, queue, goto_functions);

      // find all the symbols it uses to add declarations
      add_decl_dead(node, queue, decl_dead);
    }

    // add any required jumps
    add_jumps(queue, jumps, dep_graph.cfg_post_dominators());
  }
}

static bool implicit(goto_programt::const_targett target)
{
  // some variables are used during symbolic execution only

  const irep_idt &statement = target->get_code().get_statement();
  if(statement==ID_array_copy)
    return true;

  if(!target->is_assign())
    return false;

  const exprt &a_lhs = target->assign_lhs();
  if(a_lhs.id() != ID_symbol)
    return false;

  const symbol_exprt &s = to_symbol_expr(a_lhs);

  return s.get_identifier() == rounding_mode_identifier();
}

void full_slicert::operator()(
  goto_functionst &goto_functions,
  const namespacet &ns,
  const slicing_criteriont &criterion)
{
  // build the CFG data structure
  cfg(goto_functions);
  for(const auto &gf_entry : goto_functions.function_map)
  {
    forall_goto_program_instructions(i_it, gf_entry.second.body)
      cfg.get_node(i_it).function_id = gf_entry.first;
  }

  // fill queue with according to slicing criterion
  queuet queue;
  // gather all unconditional jumps as they may need to be included
  jumpst jumps;
  // declarations or dead instructions may be necessary as well
  decl_deadt decl_dead;

  for(const auto &instruction_and_index : cfg.entries())
  {
    const auto &instruction = instruction_and_index.first;
    const auto instruction_node_index = instruction_and_index.second;
    if(criterion(cfg[instruction_node_index].function_id, instruction))
      add_to_queue(queue, instruction_node_index, instruction);
    else if(implicit(instruction))
      add_to_queue(queue, instruction_node_index, instruction);
    else if(
      (instruction->is_goto() && instruction->condition().is_true()) ||
      instruction->is_throw())
      jumps.push_back(instruction_node_index);
    else if(instruction->is_decl())
    {
      const auto &s = instruction->decl_symbol();
      decl_dead[s.get_identifier()].push(instruction_node_index);
    }
    else if(instruction->is_dead())
    {
      const auto &s = instruction->dead_symbol();
      decl_dead[s.get_identifier()].push(instruction_node_index);
    }
  }

  // compute program dependence graph (and post-dominators)
  dependence_grapht dep_graph(ns);
  dep_graph(goto_functions, ns);

  // compute the fixedpoint
  fixedpoint(goto_functions, queue, jumps, decl_dead, dep_graph);

  // now replace those instructions that are not needed
  // by skips

  for(auto &gf_entry : goto_functions.function_map)
  {
    if(gf_entry.second.body_available())
    {
      Forall_goto_program_instructions(i_it, gf_entry.second.body)
      {
        const auto &cfg_node = cfg.get_node(i_it);
        if(
          !i_it->is_end_function() && // always retained
          !cfg_node.node_required)
        {
          i_it->turn_into_skip();
        }
#ifdef DEBUG_FULL_SLICERT
        else
        {
          std::string c="ins:"+std::to_string(i_it->location_number);
          c+=" req by:";
          for(std::set<unsigned>::const_iterator req_it =
                cfg_node.required_by.begin();
              req_it != cfg_node.required_by.end();
              ++req_it)
          {
            if(req_it != cfg_node.required_by.begin())
              c+=",";
            c+=std::to_string(*req_it);
          }
          i_it->source_location.set_column(c);  // for show-goto-functions
          i_it->source_location.set_comment(c); // for dump-c
        }
#endif
      }
    }
  }

  // remove the skips
  remove_skip(goto_functions);
}

void full_slicer(
  goto_functionst &goto_functions,
  const namespacet &ns,
  const slicing_criteriont &criterion)
{
  full_slicert()(goto_functions, ns, criterion);
}

void full_slicer(
  goto_functionst &goto_functions,
  const namespacet &ns)
{
  assert_criteriont a;
  full_slicert()(goto_functions, ns, a);
}

void full_slicer(goto_modelt &goto_model)
{
  assert_criteriont a;
  const namespacet ns(goto_model.symbol_table);
  full_slicert()(goto_model.goto_functions, ns, a);
}

void property_slicer(
  goto_functionst &goto_functions,
  const namespacet &ns,
  const std::list<std::string> &properties)
{
  properties_criteriont p(properties);
  full_slicert()(goto_functions, ns, p);
}

void property_slicer(
  goto_modelt &goto_model,
  const std::list<std::string> &properties)
{
  const namespacet ns(goto_model.symbol_table);
  property_slicer(goto_model.goto_functions, ns, properties);
}

slicing_criteriont::~slicing_criteriont()
{
}
