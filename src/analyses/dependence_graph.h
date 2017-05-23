/*******************************************************************\

Module: Field-Sensitive Program Dependence Analysis, Litvak et al.,
        FSE 2010

Author: Michael Tautschnig

Date: August 2013

\*******************************************************************/

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

  dep_graph_domaint():
    has_values(false),
    node_id(std::numeric_limits<node_indext>::max())
  {
  }

  bool merge(
    const dep_graph_domaint &src,
    goto_programt::const_targett from,
    goto_programt::const_targett to);

  void transform(
    goto_programt::const_targett from,
    goto_programt::const_targett to,
    ai_baset &ai,
    const namespacet &ns) final;

  void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const final;

  jsont output_json(
    const ai_baset &ai,
    const namespacet &ns) const override;

  void make_top() final override
  {
    assert(node_id!=std::numeric_limits<node_indext>::max());

    has_values=tvt(true);
    control_deps.clear();
    data_deps.clear();
  }

  void make_bottom() final
  {
    assert(node_id!=std::numeric_limits<node_indext>::max());

    has_values=tvt(false);
    control_deps.clear();
    data_deps.clear();
  }

  void make_entry() final
  {
    make_top();
  }

  void set_node_id(node_indext id)
  {
    node_id=id;
  }

  node_indext get_node_id() const
  {
    assert(node_id!=std::numeric_limits<node_indext>::max());
    return node_id;
  }

private:
  tvt has_values;
  node_indext node_id;

  typedef std::set<goto_programt::const_targett> depst;
  depst control_deps, data_deps;

  void control_dependencies(
    goto_programt::const_targett from,
    goto_programt::const_targett to,
    dependence_grapht &dep_graph);

  void data_dependencies(
    goto_programt::const_targett from,
    goto_programt::const_targett to,
    dependence_grapht &dep_graph,
    const namespacet &ns);
};

class dependence_grapht:
  public ait<dep_graph_domaint>,
  public grapht<dep_nodet>
{
public:
  using ait<dep_graph_domaint>::operator[];
  using grapht<dep_nodet>::operator[];

  typedef std::map<irep_idt, cfg_post_dominatorst> post_dominators_mapt;

  explicit dependence_grapht(const namespacet &_ns):
    ns(_ns),
    rd(ns)
  {
  }

  void initialize(const goto_functionst &goto_functions)
  {
    ait<dep_graph_domaint>::initialize(goto_functions);
    rd(goto_functions, ns);
  }

  void initialize(const goto_programt &goto_program)
  {
    ait<dep_graph_domaint>::initialize(goto_program);

    if(!goto_program.empty())
    {
      const irep_idt id=goto_programt::get_function_id(goto_program);
      cfg_post_dominatorst &pd=post_dominators[id];
      pd(goto_program);
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

  virtual statet &get_state(goto_programt::const_targett l)
  {
    std::pair<state_mapt::iterator, bool> entry=
      state_map.insert(std::make_pair(l, dep_graph_domaint()));

    if(entry.second)
    {
      const node_indext node_id=add_node();
      entry.first->second.set_node_id(node_id);
      nodes[node_id].PC=l;
    }

    return entry.first->second;
  }

protected:
  const namespacet &ns;

  post_dominators_mapt post_dominators;
  reaching_definitions_analysist rd;
};

#endif // CPROVER_ANALYSES_DEPENDENCE_GRAPH_H
