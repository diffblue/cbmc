/*******************************************************************\

Module: Compute natural loops in a goto_function

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

#ifndef CPROVER_NATURAL_LOOPS_H
#define CPROVER_NATURAL_LOOPS_H

#include <set>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

#include "cfg_dominators.h"

class natural_loopst
{
public:
  typedef std::set<goto_programt::const_targett> natural_loopt;

  // map loop headers to loops
  typedef std::map<goto_programt::const_targett, natural_loopt> loop_mapt;
  
  loop_mapt loop_map;

  void operator()(const goto_programt &program)
  {
    compute(program);
  }

  void output(std::ostream &) const;
  
  natural_loopst()
  {
  }

  explicit natural_loopst(const goto_programt &program)
  {
    compute(program);
  }

  const cfg_dominatorst& get_dominator_info() const
  {
    return cfg_dominators;
  }

protected:
  cfg_dominatorst cfg_dominators;

  void compute(const goto_programt &program);

  void compute_natural_loop(goto_programt::const_targett, 
                            goto_programt::const_targett);
  
};

void show_natural_loops(const goto_functionst &goto_functions);

#endif
