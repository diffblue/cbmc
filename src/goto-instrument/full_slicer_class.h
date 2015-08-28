/*******************************************************************\

Module: Goto Program Slicing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAM_FULL_SLICER_CLASS_H
#define CPROVER_GOTO_PROGRAM_FULL_SLICER_CLASS_H

#include <stack>
#include <vector>
#include <list>

#include <goto-programs/goto_functions.h>
#include <goto-programs/cfg.h>

#include <analyses/cfg_dominators.h>

class dependence_grapht;

/*******************************************************************\

   Class: full_slicert

 Purpose:

\*******************************************************************/

class full_slicert
{
public:
  void operator()(
    goto_functionst &goto_functions,
    const namespacet &ns,
    slicing_criteriont &criterion);

protected:
  struct cfg_nodet
  {
    cfg_nodet():node_required(false)
    {
    }

    bool node_required;
  };

  typedef cfg_baset<cfg_nodet> cfgt;
  cfgt cfg;

  typedef std::vector<cfgt::entryt> dep_node_to_cfgt;
  typedef std::stack<cfgt::entryt> queuet;
  typedef std::list<cfgt::entryt> jumpst;
  typedef hash_map_cont<irep_idt, queuet, irep_id_hash> decl_deadt;

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
    const cfg_post_dominatorst &cfg_post_dominators);

  inline void add_to_queue(
    queuet &queue,
    const cfgt::entryt &entry,
    goto_programt::const_targett reason)
  {
    queue.push(entry);
  }
};

class assert_criteriont:public slicing_criteriont
{
public:
  virtual bool operator()(goto_programt::const_targett target)
  {
    return target->is_assert();
  }
};

#endif
