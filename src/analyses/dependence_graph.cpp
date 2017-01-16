/*******************************************************************\

Module: Field-Sensitive Program Dependence Analysis, Litvak et al.,
        FSE 2010

Author: Michael Tautschnig

Date: August 2013

\*******************************************************************/

/// \file
/// Field-Sensitive Program Dependence Analysis, Litvak et al., FSE 2010

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <cassert>

#include <util/json.h>
#include <util/json_expr.h>

#include "goto_rw.h"

#include "dependence_graph.h"

bool dep_graph_domaint::merge(
  const dep_graph_domaint &src,
  goto_programt::const_targett from,
  goto_programt::const_targett to)
{
  bool changed=has_values.is_false() || has_changed;

  // handle data dependencies
  if((has_values.is_false() || has_changed)
      && data_deps.empty())
  {
    data_deps=src.data_deps;
  }

  changed|=merge_control_dependencies(
    src.control_deps,
    src.control_dep_candidates);

  has_changed=false;
  has_values=tvt::unknown();

  return changed;
}

void dep_graph_domaint::control_dependencies(
  goto_programt::const_targett from,
  goto_programt::const_targett to,
  dependence_grapht &dep_graph)
{
  // Better Slicing of Programs with Jumps and Switches
  // Kumar and Horwitz, FASE'02:
  // "Node N is control dependent on node M iff N postdominates, in
  // the CFG, one but not all of M's CFG successors."
  //
  // The "successor" above refers to an immediate successor of M.

  // Candidates for M for "to" are "from" and all existing control
  // dependencies on nodes. "from" is added if it is a goto or assume
  // instruction

  // Add new candidates

  if(from->is_goto() || from->is_assume())
    control_dep_candidates.insert(from);
  else if(from->is_end_function())
  {
    control_dep_candidates.clear();
    return;
  }

  if(control_dep_candidates.empty())
    return;

  // Compute postdominators if needed

  const goto_functionst &goto_functions=dep_graph.goto_functions;

  const irep_idt id=goto_programt::get_function_id(from);
  cfg_post_dominatorst &pd_tmp=dep_graph.cfg_post_dominators()[id];

  goto_functionst::function_mapt::const_iterator f_it=
    goto_functions.function_map.find(id);

  if(f_it==goto_functions.function_map.end())
    return;

  const goto_programt &goto_program=f_it->second.body;

  if(pd_tmp.cfg.size()==0) // have we computed the dominators already?
  {
    pd_tmp(goto_program);
  }

  const cfg_post_dominatorst &pd=pd_tmp;

  // Check all candidates

  for(const auto &cd : control_dep_candidates)
  {
    // check all CFG successors of M
    // special case: assumptions also introduce a control dependency
    bool post_dom_all=!cd->is_assume();
    bool post_dom_one=false;

    // we could hard-code assume and goto handling here to improve
    // performance
    cfg_post_dominatorst::cfgt::entry_mapt::const_iterator e=
      pd.cfg.entry_map.find(cd);

    assert(e!=pd.cfg.entry_map.end());

    const cfg_post_dominatorst::cfgt::nodet &m=
      pd.cfg[e->second];

    // successors of M
    for(const auto &edge : m.out)
    {
      const cfg_post_dominatorst::cfgt::nodet &m_s=
        pd.cfg[edge.first];

      if(m_s.dominators.find(to)!=m_s.dominators.end())
        post_dom_one=true;
      else
        post_dom_all=false;
    }

    if(post_dom_all || !post_dom_one)
    {
      control_deps.erase(cd);
    }
    else
    {
      tvt branch=tvt::unknown();

      if(cd->is_goto() && !cd->is_backwards_goto())
      {
        goto_programt::const_targett t=cd->get_target();
        branch=to->location_number>=t->location_number?tvt(false):tvt(true);
      }

      control_deps.insert(std::make_pair(cd, branch));
    }
  }

  // add edges to the graph
  for(const auto &c_dep : control_deps)
    dep_graph.add_dep(dep_edget::kindt::CTRL, c_dep.first, to);
}

#if 0
void dep_graph_domaint::control_dependencies(
  goto_programt::const_targett from,
  goto_programt::const_targett to,
  dependence_grapht &dep_graph)
{
  // Better Slicing of Programs with Jumps and Switches
  // Kumar and Horwitz, FASE'02:
  // "Node N is control dependent on node M iff N postdominates, in
  // the CFG, one but not all of M's CFG successors."
  //
  // The "successor" above refers to an immediate successor of M.

  // Candidates for M for "to" are "from" and all existing control
  // dependencies on nodes. "from" is added if it is a goto or assume
  // instruction
  if(from->is_goto())
  {
    goto_programt::const_targett next=from;
    next++;

    tvt branch=next!=to?tvt(true):tvt(false);
    control_deps.insert(std::make_pair(from, branch));
  }
  else if(from->is_assume())
  {
    control_deps.insert(std::make_pair(from, tvt::unknown()));
  }

  if(control_deps.empty())
    return;

  const goto_functionst &goto_functions=dep_graph.goto_functions;

  const irep_idt id=goto_programt::get_function_id(from);
  cfg_post_dominatorst &pd_tmp=dep_graph.cfg_post_dominators()[id];

  goto_functionst::function_mapt::const_iterator f_it=
    goto_functions.function_map.find(id);

  if(f_it==goto_functions.function_map.end())
    return;

  const goto_programt &goto_program=f_it->second.body;

  if(pd_tmp.cfg.size()==0) // have we computed the dominators already?
  {
#ifdef DEBUG
    std::cout << "Computing dominators for " << id << std::endl;
#endif
    pd_tmp(goto_program);
  }

  const cfg_post_dominatorst &pd=pd_tmp;

  // check all candidates for M, with current node N=to
  for(control_depst::iterator
      it=control_deps.begin();
      it!=control_deps.end();
      ) // no ++it
  {
    const goto_programt::const_targett cd=it->first;

    // check all CFG successors of M
    // special case: assumptions also introduce a control dependency
    bool post_dom_all=!cd->is_assume();
    bool post_dom_one=false;

    // we could hard-code assume and goto handling here to improve
    // performance
    cfg_post_dominatorst::cfgt::entry_mapt::const_iterator e=
      pd.cfg.entry_map.find(cd);

    assert(e!=pd.cfg.entry_map.end());

    const cfg_post_dominatorst::cfgt::nodet &m=
      pd.cfg[e->second];

    // successors of M
    for(const auto &edge : m.out)
    {
      const cfg_post_dominatorst::cfgt::nodet &m_s=
        pd.cfg[edge.first];

      if(m_s.dominators.find(to)!=m_s.dominators.end())
        post_dom_one=true;
      else
        post_dom_all=false;
    }

    if(post_dom_all ||
       !post_dom_one)
    {
      it=control_deps.erase(it);
    }
    else
    {
      it++;
    }
  }

  // add edges to the graph
  for(const auto &c_dep : control_deps)
    dep_graph.add_dep(dep_edget::CTRL, c_dep.first, to);
}
#endif

bool dep_graph_domaint::merge_control_dependencies(
  const control_depst &other_control_deps,
  const control_dep_candidatest &other_control_dep_candidates)
{
  bool changed=false;

  // Merge control dependencies

  control_depst::iterator it=control_deps.begin();

  for(const auto &c_dep : other_control_deps)
  {
    // find position to insert
    while(it!=control_deps.end() && it->first<c_dep.first)
      ++it;

    if(it==control_deps.end() || c_dep.first<it->first)
    {
      // hint points at position that will follow the new element
      control_deps.insert(it, c_dep);
      changed=true;
    }
    else
    {
      assert(it!=control_deps.end());
      assert(!(it->first<c_dep.first));
      assert(!(c_dep.first<it->first));

      tvt &branch1=it->second;
      const tvt &branch2=c_dep.second;

      if(branch1!=branch2 && !branch1.is_unknown())
      {
        branch1=tvt::unknown();
        changed=true;
      }

      ++it;
    }
  }

  // Merge control dependency candidates

  size_t n=control_dep_candidates.size();

  control_dep_candidates.insert(
      other_control_dep_candidates.begin(),
      other_control_dep_candidates.end());

  changed|=n!=control_dep_candidates.size();

  return changed;
}

static bool may_be_def_use_pair(
  const mp_integer &w_start,
  const mp_integer &w_end,
  const mp_integer &r_start,
  const mp_integer &r_end)
{
  assert(w_start>=0);
  assert(r_start>=0);

  if((w_end!=-1 && w_end <= r_start) || // we < rs
     (r_end!=-1 && w_start >= r_end)) // re < we
    return false;
  else if(w_start >= r_start) // rs <= ws < we,re
    return true;
  else if(w_end==-1 ||
          (r_end!=-1 && w_end > r_start)) // ws <= rs < we,re
    return true;
  else
    return false;
}

void dep_graph_domaint::data_dependencies(
  goto_programt::const_targett from,
  goto_programt::const_targett to,
  dependence_grapht &dep_graph,
  const namespacet &ns)
{
  // data dependencies using def-use pairs
  data_deps.clear();

  value_setst &value_sets=
    dep_graph.reaching_definitions().get_value_sets();

  // objects read and written by instruction
  rw_range_set_value_sett rw_set(ns, value_sets);
  goto_rw(to, dep_graph.get_goto_functions(), rw_set);

  forall_rw_range_set_r_objects(it, rw_set)
  {
    const irep_idt object=it->first;

    // ranges for object
    const range_domaint &r_ranges=rw_set.get_ranges(it);

    const rd_range_domaint &rds=dep_graph.reaching_definitions()[to];

    // reaching definitions for object
    const rd_range_domaint::ranges_at_loct &w_ranges_at_locs=rds.get(object);

    for(const auto &w_ranges_at_loc : w_ranges_at_locs)
    {
      const locationt location=w_ranges_at_loc.first;
      const rd_range_domaint::rangest w_ranges=w_ranges_at_loc.second;

      for(const auto &w_range : w_ranges)
      {
        const range_spect w_left=w_range.first;
        const range_spect w_right=w_range.second;

        for(const auto &r_range : r_ranges)
        {
          const exprt &object_expr=r_range.first;

          const auto &range=r_range.second;
          const range_spect r_left=range.first;
          const range_spect r_right=range.second;

          if(may_be_def_use_pair(w_left, w_right, r_left, r_right))
          {
            // found a def-use pair
            data_deps[location].insert(object_expr);
          }
        }
      }
    }

    dep_graph.reaching_definitions()[to].clear_cache(object);
  }

  // handle return value of no body function

  if(to->is_assign())
  {
    const code_assignt &ca=to_code_assign(to->code);
    const exprt &rhs=ca.rhs();

    if(rhs.id()==ID_side_effect)
    {
      const side_effect_exprt &see=to_side_effect_expr(rhs);
      if(see.get_statement()==ID_nondet)
      {
        if(from->is_function_call())
        {
          const code_function_callt &cfc=to_code_function_call(from->code);
          const exprt &call=cfc.function();

          if(call.id()==ID_symbol)
          {
            const irep_idt id=to_symbol_expr(call).id();
            const goto_functionst &goto_functions=dep_graph.goto_functions;

            goto_functionst::function_mapt::const_iterator it=
              goto_functions.function_map.find(id);

            if(it!=goto_functions.function_map.end())
            {
              if(!it->second.body_available()) // body not available
              {
                data_deps[from].insert(call);
              }
            }
            else // function not in map
            {
              data_deps[from].insert(call);
            }
          }
          else // complex call expression
          {
            data_deps[from].insert(call);
          }
        }
      }
    }
  }

  // add edges to the graph
  for(const auto &d_dep : data_deps)
  {
    // d_dep.first might be handled in a future call call to visit only,
    // depending on the sequence of successors; make sure it exists
    dep_graph.get_state(d_dep.first);
    dep_graph.add_dep(dep_edget::kindt::DATA, d_dep.first, to);
  }
}

void dep_graph_domaint::transform(
  goto_programt::const_targett from,
  goto_programt::const_targett to,
  ai_baset &ai,
  const namespacet &ns)
{
  assert(!has_values.is_false());

  dependence_grapht *dep_graph=dynamic_cast<dependence_grapht*>(&ai);
  assert(dep_graph!=nullptr);

  // propagate control dependencies across function calls
  if(from->is_function_call())
  {
    goto_programt::const_targett next=from;
    ++next;

    if(to==next)
    {
      control_dependencies(from, to, *dep_graph);
    }
    else
    {
      dep_graph_domaint *s=
        dynamic_cast<dep_graph_domaint*>(&(dep_graph->get_state(next)));
      assert(s!=nullptr);

      if(s->has_values.is_false())
      {
        s->has_values=tvt::unknown();
        s->has_changed=true;
      }

      // modify abstract state of return location
      if(s->merge_control_dependencies(
           control_deps,
           control_dep_candidates))
        s->has_changed=true;

      control_deps.clear();
      control_dep_candidates.clear();
    }
  }
  else
    control_dependencies(from, to, *dep_graph);

  data_dependencies(from, to, *dep_graph, ns);
}

void dep_graph_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  if(!control_deps.empty())
  {
    out << "Control dependencies: ";
    for(control_depst::const_iterator
        it=control_deps.begin();
        it!=control_deps.end();
        ++it)
    {
      if(it!=control_deps.begin())
        out << ",";

      const goto_programt::const_targett cd=it->first;
      const tvt branch=it->second;

      out << cd->location_number << " [" << branch << "]";
    }
    out << "\n";
  }

  if(!data_deps.empty())
  {
    out << "Data dependencies: ";
    for(data_depst::const_iterator
        it=data_deps.begin();
        it!=data_deps.end();
        ++it)
    {
      if(it!=data_deps.begin())
        out << ", ";

      out << it->first->location_number;

      out << " [";

      const auto &expr_list=it->second;
      for(auto e_it=expr_list.begin(); e_it!=expr_list.end(); e_it++)
      {
        if(e_it!=expr_list.begin())
          out << ", ";

        out << from_expr(ns, "", *e_it);
      }

      out << "]";
    }
    out << "\n";
  }
}

/// Outputs the current value of the domain.
/// \par parameters: The abstract interpreter and the namespace.
/// \return The domain, formatted as a JSON object.
jsont dep_graph_domaint::output_json(
  const ai_baset &ai,
  const namespacet &ns) const
{
  json_arrayt graph;

  for(const auto &cd : control_deps)
  {
    const goto_programt::const_targett target=cd.first;
    const tvt branch=cd.second;

    json_objectt &link=graph.push_back().make_object();

    link["locationNumber"]=
      json_numbert(std::to_string(target->location_number));
    link["sourceLocation"]=json(target->source_location);
    link["type"]=json_stringt("control");
    link["branch"]=json_stringt(branch.to_string());
  }

  for(const auto &dd : data_deps)
  {
    goto_programt::const_targett target=dd.first;
    const std::set<exprt> &expr_set=dd.second;

    json_objectt &link=graph.push_back().make_object();
    link["locationNumber"]=
      json_numbert(std::to_string(target->location_number));
    link["sourceLocation"]=json(target->source_location);
    link["type"]=json_stringt("data");

    json_arrayt &expressions=link["expressions"].make_array();

    for(const exprt &e : expr_set)
    {
      json_objectt &object=expressions.push_back().make_object();
      object["expression"]=json_stringt(from_expr(ns, "", e));
      object["certainty"]=json_stringt("maybe");
    }
  }

  return graph;
}

void dependence_grapht::add_dep(
  dep_edget::kindt kind,
  goto_programt::const_targett from,
  goto_programt::const_targett to)
{
  const node_indext n_from=state_map[from].get_node_id();
  assert(n_from<size());
  const node_indext n_to=state_map[to].get_node_id();
  assert(n_to<size());

  // add_edge is redundant as the subsequent operations also insert
  // entries into the edge maps (implicitly)

  // add_edge(n_from, n_to);

  nodes[n_from].out[n_to].add(kind);
  nodes[n_to].in[n_from].add(kind);
}
