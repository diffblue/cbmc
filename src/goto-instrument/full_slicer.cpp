/*******************************************************************\

Module: Slicing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/find_symbols.h>
#include <util/cprover_prefix.h>
#ifdef DEBUG_FULL_SLICERT
#include <util/i2string.h>
#endif

#include <goto-programs/remove_skip.h>

#include <analyses/dependence_graph.h>

#include "full_slicer.h"
#include "full_slicer_class.h"

/*******************************************************************\

Function: full_slicert::add_dependencies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: full_slicert::add_dependencies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void full_slicert::add_function_calls(
  const cfgt::nodet &node,
  queuet &queue,
  const goto_functionst &goto_functions)
{
  goto_functionst::function_mapt::const_iterator f_it=
    goto_functions.function_map.find(node.PC->function);
  assert(f_it!=goto_functions.function_map.end());

  assert(!f_it->second.body.instructions.empty());
  goto_programt::const_targett begin_function=
    f_it->second.body.instructions.begin();

  cfgt::entry_mapt::const_iterator entry=
    cfg.entry_map.find(begin_function);
  assert(entry!=cfg.entry_map.end());

  for(cfgt::edgest::const_iterator
      it=cfg[entry->second].in.begin();
      it!=cfg[entry->second].in.end();
      ++it)
    add_to_queue(queue, it->first, node.PC);
}

/*******************************************************************\

Function: full_slicert::add_decl_dead

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void full_slicert::add_decl_dead(
  const cfgt::nodet &node,
  queuet &queue,
  decl_deadt &decl_dead)
{
  if(decl_dead.empty()) return;

  find_symbols_sett syms;
  find_symbols(node.PC->code, syms);
  find_symbols(node.PC->guard, syms);

  for(find_symbols_sett::const_iterator
      it=syms.begin();
      it!=syms.end();
      ++it)
  {
    decl_deadt::iterator entry=decl_dead.find(*it);
    if(entry==decl_dead.end()) continue;

    while(!entry->second.empty())
    {
      add_to_queue(queue, entry->second.top(), node.PC);
      entry->second.pop();
    }

    decl_dead.erase(entry);
  }
}

/*******************************************************************\

Function: full_slicert::add_jumps

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void full_slicert::add_jumps(
  queuet &queue,
  jumpst &jumps,
  const cfg_post_dominatorst &cfg_post_dominators)
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
      cfgt::entry_mapt::const_iterator entry=
        cfg.entry_map.find(lex_succ);
      assert(entry!=cfg.entry_map.end());

      if(cfg[entry->second].node_required)
        break;
    }
    if(lex_succ->is_end_function())
    {
      it=next;
      continue;
    }

    cfg_post_dominatorst::cfgt::entry_mapt::const_iterator e=
      cfg_post_dominators.cfg.entry_map.find(j.PC);
    assert(e!=cfg_post_dominators.cfg.entry_map.end());
    const cfg_post_dominatorst::cfgt::nodet &n=
      cfg_post_dominators.cfg[e->second];

    // find the nearest post-dominator in slice
    if(n.dominators.find(lex_succ)==n.dominators.end())
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
      for(cfg_dominatorst::target_sett::const_iterator
          d_it=n.dominators.begin();
          d_it!=n.dominators.end();
          ++d_it)
      {
        cfgt::entry_mapt::const_iterator entry=
          cfg.entry_map.find(*d_it);
        assert(entry!=cfg.entry_map.end());

        if(cfg[entry->second].node_required)
        {
          cfg_post_dominatorst::cfgt::entry_mapt::const_iterator e2=
            cfg_post_dominators.cfg.entry_map.find(*d_it);
          assert(e2!=cfg_post_dominators.cfg.entry_map.end());
          const cfg_post_dominatorst::cfgt::nodet &n2=
            cfg_post_dominators.cfg[e2->second];

          if(n2.dominators.size()>post_dom_size)
          {
            nearest=*d_it;
            post_dom_size=n2.dominators.size();
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

/*******************************************************************\

Function: full_slicert::fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void full_slicert::fixedpoint(
  goto_functionst &goto_functions,
  queuet &queue,
  jumpst &jumps,
  decl_deadt &decl_dead,
  const dependence_grapht &dep_graph)
{
  std::vector<cfgt::entryt> dep_node_to_cfg;
  dep_node_to_cfg.reserve(dep_graph.size());
  for(unsigned i=0; i<dep_graph.size(); ++i)
  {
    cfgt::entry_mapt::const_iterator entry=
      cfg.entry_map.find(dep_graph[i].PC);
    assert(entry!=cfg.entry_map.end());

    dep_node_to_cfg.push_back(entry->second);
  }

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

/*******************************************************************\

Function: implicit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static bool implicit(goto_programt::const_targett target)
{
  // some variables are used during symbolic execution only

  if(!target->is_assign()) return false;

  const code_assignt &a=to_code_assign(target->code);
  if(a.lhs().id()!=ID_symbol) return false;

  const symbol_exprt &s=to_symbol_expr(a.lhs());

  return s.get_identifier()==CPROVER_PREFIX "rounding_mode";
}

/*******************************************************************\

Function: full_slicert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void full_slicert::operator()(
  goto_functionst &goto_functions,
  const namespacet &ns,
  slicing_criteriont &criterion)
{
  // build the CFG data structure
  cfg(goto_functions);

  // fill queue with according to slicing criterion
  queuet queue;
  // gather all unconditional jumps as they may need to be included
  jumpst jumps;
  // declarations or dead instructions may be necessary as well
  decl_deadt decl_dead;

  for(cfgt::entry_mapt::iterator
      e_it=cfg.entry_map.begin();
      e_it!=cfg.entry_map.end();
      e_it++)
  {
    if(criterion(e_it->first))
      add_to_queue(queue, e_it->second, e_it->first);
    else if(implicit(e_it->first))
      add_to_queue(queue, e_it->second, e_it->first);
    else if((e_it->first->is_goto() && e_it->first->guard.is_true()) ||
            e_it->first->is_throw())
      jumps.push_back(e_it->second);
    else if(e_it->first->is_decl())
    {
      const exprt &s=to_code_decl(e_it->first->code).symbol();
      decl_dead[to_symbol_expr(s).get_identifier()].push(e_it->second);
    }
    else if(e_it->first->is_dead())
    {
      const exprt &s=to_code_dead(e_it->first->code).symbol();
      decl_dead[to_symbol_expr(s).get_identifier()].push(e_it->second);
    }
  }

  // compute program dependence graph (and post-dominators)
  dependence_grapht dep_graph(ns);
  dep_graph(goto_functions, ns);

  // compute the fixedpoint
  fixedpoint(goto_functions, queue, jumps, decl_dead, dep_graph);

  // now replace those instructions that are not needed
  // by skips

  Forall_goto_functions(f_it, goto_functions)
    if(f_it->second.body_available)
    {
      Forall_goto_program_instructions(i_it, f_it->second.body)
      {
        const cfgt::entryt &e=cfg.entry_map[i_it];
        if(!i_it->is_end_function() && // always retained
           !cfg[e].node_required)
          i_it->make_skip();
#ifdef DEBUG_FULL_SLICERT
        else
        {
          std::string c="ins:"+i2string(i_it->location_number);
          c+=" req by:";
          for(std::set<unsigned>::const_iterator
              req_it=cfg[e].required_by.begin();
              req_it!=cfg[e].required_by.end();
              ++req_it)
          {
            if(req_it!=cfg[e].required_by.begin()) c+=",";
            c+=i2string(*req_it);
          }
          i_it->source_location.set_column(c);  // for show-goto-functions
          i_it->source_location.set_comment(c); // for dump-c
        }
#endif
      }
    }

  // remove the skips
  remove_skip(goto_functions);
  goto_functions.update();
}

/*******************************************************************\

Function: full_slicer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void full_slicer(
  goto_functionst &goto_functions,
  const namespacet &ns,
  slicing_criteriont &criterion)
{
  full_slicert()(goto_functions, ns, criterion);
}

/*******************************************************************\

Function: full_slicer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void full_slicer(
  goto_functionst &goto_functions,
  const namespacet &ns)
{
  assert_criteriont a;
  full_slicert()(goto_functions, ns, a);
}

/*******************************************************************\

Function: slicing_criteriont::~slicing_criteriont

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

slicing_criteriont::~slicing_criteriont()
{
}

