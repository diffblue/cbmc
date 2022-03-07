/*******************************************************************\

Module: Field-Sensitive Program Dependence Analysis, Litvak et al.,
        FSE 2010

Author: Michael Tautschnig

Date: August 2013

\*******************************************************************/

/// \file
/// Field-Sensitive Program Dependence Analysis, Litvak et al., FSE 2010

#ifndef CPROVER_ANALYSES_DEPENDENCE_GRAPH_H
#define CPROVER_ANALYSES_DEPENDENCE_GRAPH_H

#include <util/graph.h>
#include <util/threeval.h>

#include "ai.h"
#include "cfg_dominators.h"
#include "reaching_definitions.h"

class dependence_grapht;

class dep_edget
{
public:
  enum class kindt { NONE, CTRL, DATA, BOTH };

  void add(kindt _kind)
  {
    switch(kind)
    {
      case kindt::NONE:
        kind=_kind;
        break;
      case kindt::DATA:
      case kindt::CTRL:
        if(kind!=_kind)
          kind=kindt::BOTH;
        break;
      case kindt::BOTH:
        break;
    }
  }

  kindt get() const
  {
    return kind;
  }

protected:
  kindt kind;
};

struct dep_nodet:public graph_nodet<dep_edget>
{
  typedef graph_nodet<dep_edget>::edget edget;
  typedef graph_nodet<dep_edget>::edgest edgest;

  goto_programt::const_targett PC;
};

class dep_graph_domaint:public ai_domain_baset
{
public:
  typedef grapht<dep_nodet>::node_indext node_indext;

  explicit dep_graph_domaint(node_indext id)
    : has_values(false), node_id(id), has_changed(false)
  {
  }

  bool merge(const dep_graph_domaint &src, trace_ptrt from, trace_ptrt to);

  void transform(
    const irep_idt &function_from,
    trace_ptrt trace_from,
    const irep_idt &function_to,
    trace_ptrt trace_to,
    ai_baset &ai,
    const namespacet &ns) final override;

  void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const final override;

  jsont output_json(
    const ai_baset &ai,
    const namespacet &ns) const override;

  void make_top() final override
  {
    DATA_INVARIANT(node_id!=std::numeric_limits<node_indext>::max(),
                   "node_id must not be valid");

    has_values=tvt(true);
    control_deps.clear();
    control_dep_candidates.clear();
    data_deps.clear();
  }

  void make_bottom() final override
  {
    DATA_INVARIANT(node_id!=std::numeric_limits<node_indext>::max(),
                   "node_id must be valid");

    has_values=tvt(false);
    control_deps.clear();
    control_dep_candidates.clear();
    data_deps.clear();

    has_changed = false;
  }

  void make_entry() final override
  {
    DATA_INVARIANT(
      node_id != std::numeric_limits<node_indext>::max(),
      "node_id must not be valid");

    has_values = tvt::unknown();
    control_deps.clear();
    control_dep_candidates.clear();
    data_deps.clear();

    has_changed = false;
  }

  bool is_top() const final override
  {
    DATA_INVARIANT(node_id!=std::numeric_limits<node_indext>::max(),
                   "node_id must be valid");

    DATA_INVARIANT(
      !has_values.is_true() ||
        (control_deps.empty() && control_dep_candidates.empty() &&
         data_deps.empty()),
      "If the domain is top, it must have no dependencies");

    return has_values.is_true();
  }

  bool is_bottom() const final override
  {
    DATA_INVARIANT(node_id!=std::numeric_limits<node_indext>::max(),
                   "node_id must be valid");

    DATA_INVARIANT(
      !has_values.is_false() ||
        (control_deps.empty() && control_dep_candidates.empty() &&
         data_deps.empty()),
      "If the domain is bottom, it must have no dependencies");

    return has_values.is_false();
  }

  node_indext get_node_id() const
  {
    assert(node_id!=std::numeric_limits<node_indext>::max());
    return node_id;
  }

  void populate_dep_graph(
    dependence_grapht &, goto_programt::const_targett) const;

private:
  tvt has_values;
  node_indext node_id;
  bool has_changed;

  typedef std::set<goto_programt::const_targett> depst;

  // Set of locations with control instructions on which the instruction at this
  // location has a control dependency on
  depst control_deps;

  // Set of locations with control instructions from which there is a path in
  // the CFG to the current location (with the locations being in the same
  // function). The set control_deps is a subset of this set.
  depst control_dep_candidates;

  // Set of locations with instructions on which the instruction at this
  // location has a data dependency on
  depst data_deps;

  friend const depst &
    dependence_graph_test_get_control_deps(const dep_graph_domaint &);
  friend const depst &
    dependence_graph_test_get_data_deps(const dep_graph_domaint &);

  void control_dependencies(
    const irep_idt &function_id,
    goto_programt::const_targett from,
    goto_programt::const_targett to,
    dependence_grapht &dep_graph);

  void data_dependencies(
    goto_programt::const_targett from,
    const irep_idt &function_to,
    goto_programt::const_targett to,
    dependence_grapht &dep_graph,
    const namespacet &ns);
};

class dep_graph_domain_factoryt;

class dependence_grapht:
  public ait<dep_graph_domaint>,
  public grapht<dep_nodet>
{
public:
  using ait<dep_graph_domaint>::operator[];
  using grapht<dep_nodet>::operator[];

  typedef std::map<irep_idt, cfg_post_dominatorst> post_dominators_mapt;

  explicit dependence_grapht(const namespacet &_ns);

  void initialize(const goto_functionst &goto_functions)
  {
    ait<dep_graph_domaint>::initialize(goto_functions);
    rd(goto_functions, ns);

    for(const auto &entry : goto_functions.function_map)
    {
      const goto_programt &goto_program = entry.second.body;
      if(!goto_program.empty())
      {
        end_function_map.emplace(
          entry.first, std::prev(goto_program.instructions.end()));
      }
    }
  }

  void initialize(const irep_idt &function, const goto_programt &goto_program)
  {
    ait<dep_graph_domaint>::initialize(function, goto_program);

    // The dependency graph requires that all nodes are explicitly created
    forall_goto_program_instructions(i_it, goto_program)
      get_state(i_it).make_bottom();

    if(!goto_program.empty())
    {
      cfg_post_dominatorst &pd = post_dominators[function];
      pd(goto_program);

      end_function_map.emplace(
        function, std::prev(goto_program.instructions.end()));
    }
  }

  void finalize()
  {
    for(const auto &location_state :
        static_cast<location_sensitive_storaget &>(*storage).internal())
    {
      std::static_pointer_cast<dep_graph_domaint>(location_state.second)
        ->populate_dep_graph(*this, location_state.first);
    }
  }

  void add_dep(
    dep_edget::kindt kind,
    goto_programt::const_targett from,
    goto_programt::const_targett to);

  const post_dominators_mapt &cfg_post_dominators() const
  {
    return post_dominators;
  }

  const reaching_definitions_analysist &reaching_definitions() const
  {
    return rd;
  }

protected:
  friend dep_graph_domain_factoryt;
  friend dep_graph_domaint;
  const namespacet &ns;

  post_dominators_mapt post_dominators;
  reaching_definitions_analysist rd;
  std::map<irep_idt, goto_programt::const_targett> end_function_map;
};

#endif // CPROVER_ANALYSES_DEPENDENCE_GRAPH_H
