/*******************************************************************\

Module: Field-Sensitive Program Dependence Analysis, Litvak et al.,
        FSE 2010

Author: Michael Tautschnig

Date: August 2013

\*******************************************************************/

#ifndef CPROVER_DEPENDENCE_GRAPH_H
#define CPROVER_DEPENDENCE_GRAPH_H

#include <util/graph.h>

#include "ai.h"
#include "cfg_dominators.h"
#include "reaching_definitions.h"

class dependence_grapht;

class dep_graph_domaint:public ai_domain_baset
{
public:
  dep_graph_domaint():node_id((unsigned)-1)
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
    const namespacet &ns);

  virtual void output(
      std::ostream &out,
      const ai_baset &ai,
      const namespacet &ns) const;

  void set_node_id(unsigned id)
  {
    node_id=id;
  }

  unsigned get_node_id() const
  {
    return node_id;
  }

protected:
  unsigned node_id;

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

class dep_edget
{
public:
  typedef enum
  {
    NONE,
    CTRL,
    DATA,
    BOTH
  } kindt;

  void add(kindt _kind)
  {
    switch(kind)
    {
      case NONE:
        kind=_kind;
        break;
      case DATA:
      case CTRL:
        if(kind!=_kind) kind=BOTH;
        break;
      case BOTH:
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

class dependence_grapht:
  public ait<dep_graph_domaint>,
  public graph<dep_nodet>
{
public:
  using ait<dep_graph_domaint>::operator[];
  using graph<dep_nodet>::operator[];

  explicit dependence_grapht(const namespacet &_ns):
    ns(_ns),
    rd(ns)
  {
  }

  void initialize(const goto_functionst &goto_functions,
		  const namespacet &ns)
  {
    ait<dep_graph_domaint>::initialize(goto_functions, ns);
    rd(goto_functions, ns);
  }

  void initialize(const goto_programt &goto_program,
		  const namespacet &ns)
  {
    post_dominators(goto_program);
  }

  void add_dep(
    dep_edget::kindt kind,
    goto_programt::const_targett from,
    goto_programt::const_targett to);

  const cfg_post_dominatorst &cfg_post_dominators() const
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
      const unsigned node_id=add_node();
      entry.first->second.set_node_id(node_id);
      nodes[node_id].PC=l;
    }

    return entry.first->second;
  }

protected:
  const namespacet &ns;

  cfg_post_dominatorst post_dominators;
  reaching_definitions_analysist rd;
};

#endif

