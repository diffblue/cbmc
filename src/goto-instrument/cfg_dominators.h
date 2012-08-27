/*******************************************************************\

Module: Compute dominators for CFG of goto_function

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

#ifndef CPROVER_CFG_DOMINATORS_H
#define CPROVER_CFG_DOMINATORS_H

#include <set>
#include <map>
#include <ostream>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_program.h>

class cfg_dominatorst
{
public:
  typedef std::set<goto_programt::const_targett> const_target_sett;

  struct nodet
  {
    const_target_sett dominators;
    goto_programt::const_targetst successors, predecessors;

    goto_programt::const_targett PC;
  };

  typedef std::map<goto_programt::const_targett, nodet> node_mapt;
  node_mapt node_map;

  void operator()(const goto_programt &program)
  {
    initialise(program);
    fixedpoint(program);
  }

  const_target_sett top;
  goto_programt::const_targett entry_node;

  void output(std::ostream&) const;

protected:
  void initialise(const goto_programt &);
  void construct_cfg(const goto_programt &);
  void construct_cfg(const goto_programt &,
                     goto_programt::const_targett PC);
  void fixedpoint(const goto_programt &);
};

std::ostream &operator << (std::ostream &out, const cfg_dominatorst &);

#endif
