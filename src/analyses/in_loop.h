#ifndef CPROVER_ANALYSES_IN_LOOP_H
#define CPROVER_ANALYSES_IN_LOOP_H

#include <goto-programs/goto_functions.h>
#include <util/config.h>
#include <analyses/natural_loops.h>
#include <util/misc_utils.h>

class in_loopt
{
public:
  in_loopt(const goto_functionst &_goto_functions)
    : goto_functions(_goto_functions)
  {
    assert(location_set.empty());
    misc::get_locations(goto_functions, location_set);
    assert(!location_set.empty());
  }

  bool is_in_loop(goto_programt::const_targett loc);

protected:
  typedef std::set<goto_programt::const_targett> target_sett;
  typedef std::map<irep_idt, target_sett> fun_mapt;

  // set of locations in a loop per function
  fun_mapt fun_map;

  const goto_functionst &goto_functions;

  // all locations in the goto functions
  target_sett location_set;

  typedef goto_functionst::goto_functiont goto_functiont;
};

#endif
