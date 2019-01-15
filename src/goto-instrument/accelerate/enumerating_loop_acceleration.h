/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_ENUMERATING_LOOP_ACCELERATION_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_ENUMERATING_LOOP_ACCELERATION_H

#include <memory>

#include <util/make_unique.h>

#include <goto-programs/goto_program.h>

#include <analyses/natural_loops.h>

#include "polynomial_accelerator.h"
#include "path_enumerator.h"
#include "all_paths_enumerator.h"
#include "sat_path_enumerator.h"


class enumerating_loop_accelerationt
{
public:
  enumerating_loop_accelerationt(
    message_handlert &message_handler,
    symbol_tablet &_symbol_table,
    goto_functionst &_goto_functions,
    goto_programt &_goto_program,
    natural_loops_mutablet::natural_loopt &_loop,
    goto_programt::targett _loop_header,
    int _path_limit,
    guard_managert &guard_manager)
    : symbol_table(_symbol_table),
      goto_functions(_goto_functions),
      goto_program(_goto_program),
      loop(_loop),
      loop_header(_loop_header),
      guard_manager(guard_manager),
      polynomial_accelerator(
        message_handler,
        symbol_table,
        goto_functions,
        guard_manager),
      path_limit(_path_limit),
      path_enumerator(util_make_unique<sat_path_enumeratort>(
        message_handler,
        symbol_table,
        goto_functions,
        goto_program,
        loop,
        loop_header,
        guard_manager))
  {
  }

  bool accelerate(path_acceleratort &accelerator);

protected:
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;
  goto_programt &goto_program;
  natural_loops_mutablet::natural_loopt &loop;
  goto_programt::targett loop_header;
  guard_managert &guard_manager;
  polynomial_acceleratort polynomial_accelerator;
  int path_limit;

  std::unique_ptr<path_enumeratort> path_enumerator;
};

#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_ENUMERATING_LOOP_ACCELERATION_H
