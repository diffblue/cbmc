/*******************************************************************\

Module: Field-Sensitive Program Dependence Analysis, Litvak et al.,
        FSE 2010

Author: Michael Tautschnig

Date: August 2013

\*******************************************************************/

#include <cassert>

#include <util/json.h>

#include "goto_rw.h"

#include "dependence_graph.h"

/*******************************************************************\

Function: dep_graph_domaint::merge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool dep_graph_domaint::merge(
  const dep_graph_domaint &src,
  goto_programt::const_targett from,
  goto_programt::const_targett to)
{
  bool changed=has_values.is_false();
  has_values=tvt::unknown();

  depst::iterator it=control_deps.begin();
  for(const auto &c_dep : src.control_deps)
  {
    while(it!=control_deps.end() && *it<c_dep)
      ++it;
    if(it==control_deps.end() || c_dep<*it)
    {
      control_deps.insert(it, c_dep);
      changed=true;
    }
    else if(it!=control_deps.end())
      ++it;
  }

  it=data_deps.begin();
  for(const auto &d_dep : src.data_deps)
  {
    while(it!=data_deps.end() && *it<d_dep)
      ++it;
    if(it==data_deps.end() || d_dep<*it)
    {
      data_deps.insert(it, d_dep);
      changed=true;
    }
    else if(it!=data_deps.end())
      ++it;
  }

  return changed;
}

/*******************************************************************\

Function: dep_graph_domaint::control_dependencies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dep_graph_domaint::control_dependencies(
  goto_programt::const_targett from,
  goto_programt::const_targett to,
  dependence_grapht &dep_graph)
{
  // Better Slicing of Programs with Jumps and Switches
  // Kumar and Horwitz, FASE'02:
  // Node N is control dependent on node M iff N postdominates one
  // but not all of M's CFG successors.
  //
  // candidates for M are from and all existing control-depended on
  // nodes; from is added if it is a goto or assume instruction
  if(from->is_goto() ||
     from->is_assume())
    control_deps.insert(from);

  const irep_idt id=goto_programt::get_function_id(from);
  const cfg_post_dominatorst &pd=dep_graph.cfg_post_dominators().at(id);

  // check all candidates for M
  for(depst::iterator
      it=control_deps.begin();
      it!=control_deps.end();
      ) // no ++it
  {
    depst::iterator next=it;
    ++next;

    // check all CFG successors
    // special case: assumptions also introduce a control dependency
    bool post_dom_all=!(*it)->is_assume();
    bool post_dom_one=false;

    // we could hard-code assume and goto handling here to improve
    // performance
    cfg_post_dominatorst::cfgt::entry_mapt::const_iterator e=
      pd.cfg.entry_map.find(*it);

    assert(e!=pd.cfg.entry_map.end());

    const cfg_post_dominatorst::cfgt::nodet &m=
      pd.cfg[e->second];

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
      control_deps.erase(it);

    it=next;
  }

  // add edges to the graph
  for(const auto &c_dep : control_deps)
    dep_graph.add_dep(dep_edget::CTRL, c_dep, to);
}

/*******************************************************************\

Function: may_be_def_use_pair

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: dep_graph_domaint::data_depdendencies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dep_graph_domaint::data_dependencies(
  goto_programt::const_targett from,
  goto_programt::const_targett to,
  dependence_grapht &dep_graph,
  const namespacet &ns)
{
  // data dependencies using def-use pairs
  data_deps.clear();

  // TODO use (future) reaching-definitions-dereferencing rw_set
  value_setst &value_sets=
    dep_graph.reaching_definitions().get_value_sets();
  rw_range_set_value_sett rw_set(ns, value_sets);
  goto_rw(to, rw_set);

  forall_rw_range_set_r_objects(it, rw_set)
  {
    const range_domaint &r_ranges=rw_set.get_ranges(it);
    const rd_range_domaint::ranges_at_loct &w_ranges=
      dep_graph.reaching_definitions()[to].get(it->first);

    for(const auto &w_range : w_ranges)
    {
      bool found=false;
      for(const auto &wr : w_range.second)
        for(const auto &r_range : r_ranges)
          if(!found &&
             may_be_def_use_pair(wr.first, wr.second,
                                 r_range.first, r_range.second))
          {
            // found a def-use pair
            data_deps.insert(w_range.first);
            found=true;
          }
    }

    dep_graph.reaching_definitions()[to].clear_cache(it->first);
  }

  // add edges to the graph
  for(const auto &d_dep : data_deps)
  {
    // *it might be handled in a future call call to visit only,
    // depending on the sequence of successors; make sure it exists
    dep_graph.get_state(d_dep);
    dep_graph.add_dep(dep_edget::DATA, d_dep, to);
  }
}

/*******************************************************************\

Function: dep_graph_domaint::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dep_graph_domaint::transform(
  goto_programt::const_targett from,
  goto_programt::const_targett to,
  ai_baset &ai,
  const namespacet &ns)
{
  dependence_grapht *dep_graph=dynamic_cast<dependence_grapht*>(&ai);
  assert(dep_graph!=nullptr);

  // propagate control dependencies across function calls
  if(from->is_function_call())
  {
    goto_programt::const_targett next=from;
    ++next;

    if(next==to)
    {
      control_dependencies(from, to, *dep_graph);
    }
    else
    {
      // edge to function entry point

      dep_graph_domaint *s=
        dynamic_cast<dep_graph_domaint*>(&(dep_graph->get_state(next)));
      assert(s!=nullptr);

      depst::iterator it=s->control_deps.begin();
      for(const auto &c_dep : control_deps)
      {
        while(it!=s->control_deps.end() && *it<c_dep)
          ++it;
        if(it==s->control_deps.end() || c_dep<*it)
          s->control_deps.insert(it, c_dep);
        else if(it!=s->control_deps.end())
          ++it;
      }

      control_deps.clear();
    }
  }
  else
    control_dependencies(from, to, *dep_graph);

  data_dependencies(from, to, *dep_graph, ns);
}

/*******************************************************************\

Function: dep_graph_domaint::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dep_graph_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  if(!control_deps.empty())
  {
    out << "Control dependencies: ";
    for(depst::const_iterator
        it=control_deps.begin();
        it!=control_deps.end();
        ++it)
    {
      if(it!=control_deps.begin())
        out << ",";
      out << (*it)->location_number;
    }
    out << std::endl;
  }

  if(!data_deps.empty())
  {
    out << "Data dependencies: ";
    for(depst::const_iterator
        it=data_deps.begin();
        it!=data_deps.end();
        ++it)
    {
      if(it!=data_deps.begin())
        out << ",";
      out << (*it)->location_number;
    }
    out << std::endl;
  }
}

/*******************************************************************\

Function: dep_graph_domaint::output_json

  Inputs: The abstract interpreter and the namespace.

 Outputs: The domain, formatted as a JSON object.

 Purpose: Outputs the current value of the domain.

\*******************************************************************/


jsont dep_graph_domaint::output_json(
  const ai_baset &ai,
  const namespacet &ns) const
{
  json_arrayt graph;

  for(dep_graph_domaint::depst::const_iterator cdi=control_deps.begin();
      cdi!=control_deps.end();
      ++cdi)
  {
    json_objectt &link=graph.push_back().make_object();
    link["location_number"]=
      json_numbert(std::to_string((*cdi)->location_number));
    link["source_location"]=
      json_stringt((*cdi)->source_location.as_string());
    link["type"]=json_stringt("control");
  }

  for(dep_graph_domaint::depst::const_iterator ddi=data_deps.begin();
      ddi!=data_deps.end();
      ++ddi)
  {
    json_objectt &link=graph.push_back().make_object();
    link["location_number"]=
      json_numbert(std::to_string((*ddi)->location_number));
    link["source_location"]=
      json_stringt((*ddi)->source_location.as_string());
    link["type"]=json_stringt("data");
  }

  return graph;
}



/*******************************************************************\

Function: dependence_grapht::add_dep

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
