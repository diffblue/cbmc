/*******************************************************************\

 Module: analyses variable-sensitivity variable-sensitivity-dependence-graph

 Author: Diffblue Ltd.

\*******************************************************************/

#include "data_dependency_context.h"
#include "variable_sensitivity_dependence_graph.h"

#include <langapi/language_util.h>
#include <util/json.h>
#include <goto-programs/json_expr.h>
#include <util/json_irep.h>


/**
 * Evaluate an expression and accumulate all the data dependencies
 * involved in the evaluation.
 *
 * \param expr the expression to evaluate
 * \param ns the namespace to use
 * \param deps the destination in which to accumlate data dependencies
 */
void variable_sensitivity_dependence_domaint::eval_data_deps(
  const exprt &expr, const namespacet &ns, data_depst &deps) const
{
  const auto res=
    std::dynamic_pointer_cast<const data_dependency_contextt>(eval(expr, ns));

  if(res->get_data_dependencies().size() > 0)
  {
    // If the expression was able to be eval'ed to something with data
    // dependencies, then that's all we need to gather.
    for (const auto dep : res->get_data_dependencies())
      deps[dep].insert(expr);
  }
  else
  {
    // If the expression could not be eval'ed to something with data
    // dependencies, then it may have been some sort of compound expression,
    // so attempt to eval the data dependencies for all the operands, taking
    // the union of them all.
    for(const exprt &op : expr.operands())
    {
      eval_data_deps(op, ns, deps);
    }
  }
}

/**
 * Compute the abstract transformer for a single instruction. For
 * the data dependencies, this involves calculating all the data
 * dependencies that exist in the 'to' instruction.
 *
 * \param function_from the function of the instruction before the abstract
 *   domain
 * \param from the instruction before the abstract domain
 * \param function_to the function of the instruction after the abstract domain
 * \param to the instruction after the abstract domain
 * \param ai the abstract interpreter
 * \param ns the namespace
 */
void variable_sensitivity_dependence_domaint::transform(
  const irep_idt &function_from,
  locationt from,
  const irep_idt &function_to,
  locationt to,
  ai_baset &ai,
   const namespacet &ns)
{
  variable_sensitivity_domaint::transform(
    function_from, from, function_to, to, ai, ns);

  variable_sensitivity_dependence_grapht *dep_graph=
    dynamic_cast<variable_sensitivity_dependence_grapht*>(&ai);
  assert(dep_graph!=nullptr);

  // propagate control dependencies across function calls
  if(from->is_function_call())
  {
    if(function_from == function_to)
    {
      control_dependencies(function_from, from, function_to, to, *dep_graph);
    }
    else
    {
      // edge to function entry point
      const goto_programt::const_targett next = std::next(from);

      variable_sensitivity_dependence_domaint *s=
        dynamic_cast<variable_sensitivity_dependence_domaint*>
          (&(dep_graph->get_state(next)));
      assert(s!=nullptr);

      if(s->has_values.is_false())
      {
        s->has_values=tvt::unknown();
        s->has_changed=true;
      }

      // modify abstract state of return location
      if(s->merge_control_dependencies(
           control_deps,
           control_dep_candidates,
           control_dep_calls,
           control_dep_call_candidates))
        s->has_changed=true;

      control_deps.clear();
      control_dep_candidates.clear();

      control_dep_calls.clear();
      control_dep_calls.insert(from);

      control_dep_call_candidates.clear();
      control_dep_call_candidates.insert(from);
    }
  }
  else
    control_dependencies(function_from, from, function_to, to, *dep_graph);

  // Find all the data dependencies in the the 'to' expression
  data_dependencies(from, to, *dep_graph, ns);
}

void variable_sensitivity_dependence_domaint::data_dependencies(
  goto_programt::const_targett from,
  goto_programt::const_targett to,
  variable_sensitivity_dependence_grapht &dep_graph,
  const namespacet &ns)
{
  // Find all the data dependencies in the the 'to' expression
  domain_data_deps.clear();
  if(to->is_assign())
  {
    const code_assignt &inst = to_code_assign(to->code);
    const exprt &rhs=inst.rhs();

    // Handle return value of a 'no body' function
    if(rhs.id() == ID_side_effect)
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
                domain_data_deps[from].insert(call);
              }
            }
            else // function not in map
            {
              domain_data_deps[from].insert(call);
            }
          }
          else // complex call expression
          {
            domain_data_deps[from].insert(call);
          }
        }
      }
    }
    else
    {
      // Just an ordinary assignement
      eval_data_deps(rhs, ns, domain_data_deps);
    }
  }
  else if (to->is_function_call())
  {
    const code_function_callt &call = to_code_function_call(to->code);
    const code_function_callt::argumentst &args= call.arguments();
    for(const auto arg : args)
    {
      eval_data_deps(arg, ns, domain_data_deps);
    }
  }
  else if (to->is_goto())
  {
    eval_data_deps(to->guard, ns, domain_data_deps);
  }
}

void variable_sensitivity_dependence_domaint::control_dependencies(
  const irep_idt &from_function,
  goto_programt::const_targett from,
  const irep_idt &to_function,
  goto_programt::const_targett to,
  variable_sensitivity_dependence_grapht &dep_graph)
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
    control_deps.clear();
    control_dep_candidates.clear();
    control_dep_calls.clear();
    control_dep_call_candidates.clear();
    return;
  }

  // Compute postdominators if needed

  const goto_functionst &goto_functions=dep_graph.goto_functions;

  const irep_idt id = from_function;
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
    const cfg_post_dominatorst::cfgt::nodet &m=
      pd.get_node(cd);

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

  if(control_deps.empty())
  {
    util_inplace_set_union(control_dep_calls, control_dep_call_candidates);
  }
  else
  {
    control_dep_calls.clear();
  }

  // add edges to the graph
  for(const auto &c_dep : control_deps)
    dep_graph.add_dep(vs_dep_edget::kindt::CTRL, c_dep.first, to);
}

bool variable_sensitivity_dependence_domaint::merge_control_dependencies(
  const control_depst &other_control_deps,
  const control_dep_candidatest &other_control_dep_candidates,
  const control_dep_callst &other_control_dep_calls,
  const control_dep_callst &other_control_dep_call_candidates)
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

  // Merge call control dependencies

  n=control_dep_calls.size();

  control_dep_calls.insert(
      other_control_dep_calls.begin(),
      other_control_dep_calls.end());

  changed|=n!=control_dep_calls.size();

  // Merge call control dependency candidates

  n=control_dep_call_candidates.size();

  control_dep_call_candidates.insert(
      other_control_dep_call_candidates.begin(),
      other_control_dep_call_candidates.end());

   changed|=n!=control_dep_call_candidates.size();

  return changed;
}

/**
 * Computes the join between "this" and "b"
 *
 * \param b the other domain
 * \param from the location preceding the 'b' domain
 * \param to the current location
 * \return true if something has changed in the merge
 */
bool variable_sensitivity_dependence_domaint::merge(
    const variable_sensitivity_domaint &b,
    locationt from,
    locationt to)
{
  bool changed = false;

  changed = variable_sensitivity_domaint::merge(b, from, to);
  changed |= has_values.is_false() || has_changed;

  // Handle data dependencies
  const auto& cast_b =
    dynamic_cast<const variable_sensitivity_dependence_domaint&>(b);

  // Merge data dependencies
  for (auto bdep : cast_b.domain_data_deps)
  {
    for(exprt bexpr : bdep.second)
    {
      auto result = domain_data_deps[bdep.first].insert(bexpr);
      changed |= result.second;
    }
  }

  changed |= merge_control_dependencies(
    cast_b.control_deps,
    cast_b.control_dep_candidates,
    cast_b.control_dep_calls,
    cast_b.control_dep_call_candidates);

  has_changed=false;
  has_values=tvt::unknown();

  return changed;
}

/**
 * Perform a context aware merge of the changes that have been applied
 * between function_start and the current state. Anything that has not been
 * modified will be taken from the \p function_call domain.
 *
 * \param function_call: The local of the merge - values from here will be
 *   taken if they have not been modified
 * \param function_start: The base of the merge - changes that have been made
 *   between here and the end will be retained.
 * \param function_end: The end of the merge - changes that have been made
///   between the start and here will be retained.
 * \param ns: The global namespace
 */
void variable_sensitivity_dependence_domaint::merge_three_way_function_return(
  const ai_domain_baset &function_call,
  const ai_domain_baset &function_start,
  const ai_domain_baset &function_end,
  const namespacet &ns)
{
  // The gathering of the data dependencies for the domain is handled by the
  // 'transform' and simply relies on the underlying domains with their
  // data_dependency_context to be correct. Therefore all we need to ensure at
  // the three way merge is that the underlying variable sensitivity domain
  // does its three way merge.
  variable_sensitivity_domaint::merge_three_way_function_return(
    function_call,
    function_start,
    function_end,
    ns);
}

/**
 * Basic text output of the abstract domain
 *
 * \param out the stream to output onto
 * \param ai the abstract domain
 * \param ns the namespace
 */
void variable_sensitivity_dependence_domaint::output(
   std::ostream &out,
   const ai_baset &ai,
   const namespacet &ns) const
{
  if(!control_deps.empty() || !control_dep_calls.empty())
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

    for(control_dep_callst::const_iterator
        it=control_dep_calls.begin();
        it!=control_dep_calls.end();
        ++it)
    {
      if(!control_deps.empty() || it!=control_dep_calls.begin())
        out << ",";

      out << (*it)->location_number << " [UNCONDITIONAL]";
    }

    out << "\n";
  }

  if(!domain_data_deps.empty())
  {
      out << "Data dependencies: ";
      bool first = true;
      for (auto &dep : domain_data_deps)
      {
        if(!first)
          out << ", ";

        out << dep.first->location_number;
        out << " [";
        bool first_expr = true;
        for (auto &expr : dep.second)
        {
          if (!first_expr)
            out << ", ";

          out << from_expr(ns, "", expr);
          first_expr = false;
        }
        out << "]";

        first = false;
      }
      out << std::endl;
    }
}

/**
 * \brief Outputs the current value of the domain.
 *
 * \param ai the abstract interpreter
 * \param ns the namespace
 *
 * \return the domain, formatted as a JSON object.
 */
jsont variable_sensitivity_dependence_domaint::output_json(
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

  for(const auto &target : control_dep_calls)
  {
    json_objectt &link=graph.push_back().make_object();
    link["locationNumber"]=
      json_numbert(std::to_string(target->location_number));
    link["sourceLocation"]=json(target->source_location);
    link["type"]=json_stringt("control");
    link["branch"]=json_stringt("UNCONDITIONAL");
  }

  for(const auto &dep : domain_data_deps)
  {
    json_objectt &link=graph.push_back().make_object();
    link["locationNumber"]=
      json_numbert(std::to_string(dep.first->location_number));
    link["sourceLocation"]=json(dep.first->source_location);
    json_stringt(dep.first->source_location.as_string());
    link["type"]=json_stringt("data");

    const std::set<exprt> &expr_set=dep.second;
    json_arrayt &expressions=link["expressions"].make_array();

    for(const exprt &e : expr_set)
    {
      json_objectt &object=expressions.push_back().make_object();
      object["expression"]=json_stringt(from_expr(ns, "", e));
      object["certainty"]=json_stringt("maybe");
    }
  }

  return std::move(graph);
}

void variable_sensitivity_dependence_domaint::populate_dep_graph(
  variable_sensitivity_dependence_grapht &dep_graph,
  goto_programt::const_targett this_loc) const
{
  for(const auto &c_dep : control_deps)
    dep_graph.add_dep(vs_dep_edget::kindt::CTRL, c_dep.first, this_loc);

  for(const auto &c_dep : control_dep_calls)
    dep_graph.add_dep(vs_dep_edget::kindt::CTRL, c_dep, this_loc);

  for(const auto &d_dep : domain_data_deps)
    dep_graph.add_dep(vs_dep_edget::kindt::DATA, d_dep.first, this_loc);
}

void variable_sensitivity_dependence_grapht::add_dep(
  vs_dep_edget::kindt kind,
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
