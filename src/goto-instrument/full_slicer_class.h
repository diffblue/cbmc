/*******************************************************************\

Module: Goto Program Slicing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Goto Program Slicing

#ifndef CPROVER_GOTO_INSTRUMENT_FULL_SLICER_CLASS_H
#define CPROVER_GOTO_INSTRUMENT_FULL_SLICER_CLASS_H

#include <stack>
#include <vector>
#include <list>

#include <goto-programs/goto_functions.h>
#include <goto-programs/cfg.h>

#include <analyses/dependence_graph.h>

#include "full_slicer.h"

// #define DEBUG_FULL_SLICERT
#if 0
useful for debugging (remove NOLINT)
goto-instrument --full-slice a.out c.out
goto-instrument --show-goto-functions c.out > c.goto
echo 'digraph g {' > c.dot ; cat c.goto | \
  NOLINT(*) grep 'ins:[[:digit:]]\+ req by' | grep '^[[:space:]]*//' | \
  NOLINT(*) perl -n -e '/file .*(.) line (\d+) column ins:(\d+) req by:([\d,]+).*/; $f=$3; $t=$4; @tt=split(",",$t); print "n$f [label=\"$f\"];\n"; print "n$f -> n$_;\n" foreach(@tt);' >> c.dot ; \
  echo '}' >> c.dot ; tred c.dot > c-red.dot ; \
  dot -Tpdf -oc-red.pdf c-red.dot
#endif

class full_slicert
{
public:
  void operator()(
    goto_functionst &goto_functions,
    const namespacet &ns,
    const slicing_criteriont &criterion);

protected:
  struct cfg_nodet
  {
    cfg_nodet():node_required(false)
    {
    }

    bool node_required;
#ifdef DEBUG_FULL_SLICERT
    std::set<unsigned> required_by;
#endif
  };

  typedef cfg_baset<cfg_nodet> cfgt;
  cfgt cfg;

  typedef std::vector<cfgt::entryt> dep_node_to_cfgt;
  typedef std::stack<cfgt::entryt> queuet;
  typedef std::list<cfgt::entryt> jumpst;
  typedef std::unordered_map<irep_idt, queuet> decl_deadt;

  void fixedpoint(
    goto_functionst &goto_functions,
    queuet &queue,
    jumpst &jumps,
    decl_deadt &decl_dead,
    const dependence_grapht &dep_graph);

  void add_dependencies(
    const cfgt::nodet &node,
    queuet &queue,
    const dependence_grapht &dep_graph,
    const dep_node_to_cfgt &dep_node_to_cfg);

  void add_function_calls(
    const cfgt::nodet &node,
    queuet &queue,
    const goto_functionst &goto_functions);

  void add_decl_dead(
    const cfgt::nodet &node,
    queuet &queue,
    decl_deadt &decl_dead);

  void add_jumps(
    queuet &queue,
    jumpst &jumps,
    const dependence_grapht::post_dominators_mapt &post_dominators);

  void add_to_queue(
    queuet &queue,
    const cfgt::entryt &entry,
    goto_programt::const_targett reason)
  {
#ifdef DEBUG_FULL_SLICERT
    cfg[entry].required_by.insert(reason->location_number);
#else
    (void)reason; // unused parameter
#endif
    queue.push(entry);
  }
};

class assert_criteriont:public slicing_criteriont
{
public:
  virtual bool operator()(goto_programt::const_targett target) const
  {
    return target->is_assert();
  }
};

class in_function_criteriont : public slicing_criteriont
{
public:
  explicit in_function_criteriont(const std::string &function_name)
    : target_function(function_name)
  {
  }

  virtual bool operator()(goto_programt::const_targett target) const
  {
    return target->function == target_function;
  }

protected:
  const irep_idt target_function;
};

class properties_criteriont:public slicing_criteriont
{
public:
  explicit properties_criteriont(
    const std::list<std::string> &properties):
    property_ids(properties)
  {
  }

  virtual bool operator()(goto_programt::const_targett target) const
  {
    if(!target->is_assert())
      return false;

    const std::string &p_id=
      id2string(target->source_location.get_property_id());

    for(std::list<std::string>::const_iterator
        it=property_ids.begin();
        it!=property_ids.end();
        ++it)
      if(p_id==*it)
        return true;

    return false;
  }

protected:
  const std::list<std::string> &property_ids;
};

#endif // CPROVER_GOTO_INSTRUMENT_FULL_SLICER_CLASS_H
