/*******************************************************************\

Module: Field-Sensitive Program Dependence Analysis, Litvak et al.,
        FSE 2010

Author: Michael Tautschnig

Date: August 2013

\*******************************************************************/

/// \file
/// Field-Sensitive Program Dependence Analysis, Litvak et al., FSE 2010

#include "dependence_graph.h"

#include <cassert>

#include <util/container_utils.h>
#include <util/json_irep.h>

#include "goto_rw.h"

bool dep_graph_domaint::merge(
  const dep_graph_domaint &src,
  goto_programt::const_targett,
  goto_programt::const_targett)
{
  // An abstract state at location `to` may be non-bottom even if
  // `merge(..., `to`) has not been called so far. This is due to the special
  // handling of function entry edges (see transform()).
  bool changed = is_bottom() || has_changed;

  // For computing the data dependencies, we would not need a fixpoint
  // computation. The data dependencies at a location are computed from the
  // result of the reaching definitions analysis at that location
  // (in data_dependencies()). Thus, we only need to set the data dependencies
  // part of an abstract state at a certain location once.
  if(changed && data_deps.empty())
  {
    data_deps = src.data_deps;
    has_values = tvt::unknown();
  }

  changed |= util_inplace_set_union(control_deps, src.control_deps);
  changed |=
    util_inplace_set_union(control_dep_candidates, src.control_dep_candidates);

  has_changed = false;

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
  //
  // When computing the control dependencies of a node N (i.e., "to"
  // being N), candidates for M are all control statements (gotos or
  // assumes) from which there is a path in the CFG to N.

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

  // Get postdominators

  const irep_idt id=from->function;
  const cfg_post_dominatorst &pd=dep_graph.cfg_post_dominators().at(id);

  // Check all candidates

  for(const auto &control_dep_candidate : control_dep_candidates)
  {
    // check all CFG successors of M
    // special case: assumptions also introduce a control dependency
    bool post_dom_all = !control_dep_candidate->is_assume();
    bool post_dom_one=false;

    // we could hard-code assume and goto handling here to improve
    // performance
    cfg_post_dominatorst::cfgt::entry_mapt::const_iterator e =
      pd.cfg.entry_map.find(control_dep_candidate);

    INVARIANT(
      e != pd.cfg.entry_map.end(), "cfg must have an entry for every location");

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
      control_deps.erase(control_dep_candidate);
    }
    else
    {
      control_deps.insert(control_dep_candidate);
    }
  }
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
  goto_programt::const_targett,
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
  goto_rw(to->function, to, rw_set);

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
}

void dep_graph_domaint::transform(
  const irep_idt &function_from,
  goto_programt::const_targett from,
  const irep_idt &function_to,
  goto_programt::const_targett to,
  ai_baset &ai,
  const namespacet &ns)
{
  dependence_grapht *dep_graph=dynamic_cast<dependence_grapht*>(&ai);
  assert(dep_graph!=nullptr);

  // propagate control dependencies across function calls
  if(from->is_function_call())
  {
    if(function_from == function_to)
    {
      control_dependencies(from, to, *dep_graph);
    }
    else
    {
      // edge to function entry point
      const goto_programt::const_targett next = std::next(from);

      dep_graph_domaint *s=
        dynamic_cast<dep_graph_domaint*>(&(dep_graph->get_state(next)));
      assert(s!=nullptr);

      if(s->is_bottom())
      {
        s->has_values = tvt::unknown();
        s->has_changed = true;
      }

      s->has_changed |= util_inplace_set_union(s->control_deps, control_deps);
      s->has_changed |= util_inplace_set_union(
        s->control_dep_candidates, control_dep_candidates);

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
  const ai_baset &,
  const namespacet &) const
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
    out << '\n';
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
    out << '\n';
  }
}

/// Outputs the current value of the domain.
/// \par parameters: The abstract interpreter and the namespace.
/// \return The domain, formatted as a JSON object.
jsont dep_graph_domaint::output_json(
  const ai_baset &,
  const namespacet &) const
{
  json_arrayt graph;

  for(const auto &cd : control_deps)
  {
    json_objectt link(
      {{"locationNumber", json_numbert(std::to_string(cd->location_number))},
       {"sourceLocation", json(cd->source_location)},
       {"type", json_stringt("control")}});
    graph.push_back(std::move(link));
  }

  for(const auto &dd : data_deps)
  {
    json_objectt link(
      {{"locationNumber", json_numbert(std::to_string(dd->location_number))},
       {"sourceLocation", json(dd->source_location)},
       {"type", json_stringt("data")}});
    graph.push_back(std::move(link));
  }

  return std::move(graph);
}

void dependence_grapht::add_dep(
  dep_edget::kindt kind,
  goto_programt::const_targett from,
  goto_programt::const_targett to)
{
  const node_indext n_from = (*this)[from].get_node_id();
  assert(n_from<size());
  const node_indext n_to = (*this)[to].get_node_id();
  assert(n_to<size());

  // add_edge is redundant as the subsequent operations also insert
  // entries into the edge maps (implicitly)
  // add_edge(n_from, n_to);
  nodes[n_from].out[n_to].add(kind);
  nodes[n_to].in[n_from].add(kind);
}

void dep_graph_domaint::populate_dep_graph(
  dependence_grapht &dep_graph, goto_programt::const_targett this_loc) const
{
  for(const auto &c_dep : control_deps)
    dep_graph.add_dep(dep_edget::kindt::CTRL, c_dep, this_loc);

  for(const auto &d_dep : data_deps)
    dep_graph.add_dep(dep_edget::kindt::DATA, d_dep, this_loc);
}
