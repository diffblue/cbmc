/*******************************************************************\

Module: Compute natural loops in a goto_function

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

#ifndef CPROVER_NATURAL_LOOPS_H
#define CPROVER_NATURAL_LOOPS_H

#include <set>

#include <goto_program.h>

#include "cfg_dominators.h"

class natural_loopst
{
public:
  typedef std::set<goto_programt::const_targett> natural_loopt;

  // map loop headers to loops
  typedef std::map<goto_programt::const_targett, natural_loopt> loop_mapt;
  
  loop_mapt loop_map;

  void operator()(const goto_programt &program);

  void output(std::ostream&) const;

protected:
  cfg_dominatorst cfg_dominators;

  void compute_natural_loop(goto_programt::const_targett, 
                            goto_programt::const_targett);
  
};

#endif
