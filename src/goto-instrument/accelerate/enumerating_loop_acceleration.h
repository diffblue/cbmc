#ifndef ENUMERATING_LOOP_ACCELERATION_H
#define  ENUMERATING_LOOP_ACCELERATION_H

#include <goto-programs/goto_program.h>

#include <analyses/natural_loops.h>

#include "loop_acceleration.h"
#include "polynomial_accelerator.h"
#include "path_enumerator.h"


class enumerating_loop_accelerationt : public loop_accelerationt {
 public:
  enumerating_loop_accelerationt(
      symbol_tablet &_symbol_table,
      goto_functionst &_goto_functions,
      goto_programt &_goto_program,
      natural_loops_mutablet::natural_loopt &_loop,
      goto_programt::targett _loop_header) :
    symbol_table(_symbol_table),
    goto_functions(_goto_functions),
    goto_program(_goto_program),
    loop(_loop),
    loop_header(_loop_header),
    path_enumerator(_goto_program, _loop, _loop_header),
    polynomial_accelerator(symbol_table, goto_functions)
  {
  }

  virtual bool accelerate(path_acceleratort &accelerator);

 protected:
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;
  goto_programt &goto_program;
  natural_loops_mutablet::natural_loopt &loop;
  goto_programt::targett loop_header;
  path_enumeratort path_enumerator;
  polynomial_acceleratort polynomial_accelerator;
};

#endif // ENUMERATING_LOOP_ACCELERATION_H
