/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_SAT_PATH_ENUMERATOR_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_SAT_PATH_ENUMERATOR_H

#include <map>
#include <set>

#include <util/symbol_table.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

#include <analyses/natural_loops.h>

#include "path_enumerator.h"
#include "scratch_program.h"
#include "polynomial.h"
#include "path.h"
#include "accelerator.h"
#include "cone_of_influence.h"
#include "acceleration_utils.h"

class sat_path_enumeratort:public path_enumeratort
{
public:
  sat_path_enumeratort(
    message_handlert &message_handler,
    symbol_tablet &_symbol_table,
    goto_functionst &_goto_functions,
    goto_programt &_goto_program,
    natural_loops_mutablet::natural_loopt &_loop,
    goto_programt::targett _loop_header,
    guard_managert &guard_manager)
    : message_handler(message_handler),
      symbol_table(_symbol_table),
      ns(symbol_table),
      goto_functions(_goto_functions),
      goto_program(_goto_program),
      loop(_loop),
      loop_header(_loop_header),
      utils(symbol_table, message_handler, goto_functions, loop_counter),
      guard_manager(guard_manager)
  {
    find_distinguishing_points();
    build_fixed();
  }

  bool next(patht &path);

protected:
  message_handlert &message_handler;
  void find_distinguishing_points();

  void build_path(scratch_programt &scratch_program, patht &path);
  void build_fixed();

  void record_path(scratch_programt &scratch_program);

  symbol_tablet &symbol_table;
  namespacet ns;
  goto_functionst &goto_functions;
  goto_programt &goto_program;
  natural_loops_mutablet::natural_loopt &loop;
  goto_programt::targett loop_header;

  typedef std::map<goto_programt::targett, exprt> distinguish_mapt;
  typedef std::map<exprt, bool> distinguish_valuest;

  acceleration_utilst utils;
  guard_managert &guard_manager;
  exprt loop_counter;
  distinguish_mapt distinguishing_points;
  std::list<exprt> distinguishers;
  expr_sett modified;
  goto_programt fixed;
  std::list<distinguish_valuest> accelerated_paths;
};

#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_SAT_PATH_ENUMERATOR_H
