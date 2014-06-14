#ifndef ENUMERATING_LOOP_ACCELERATION_H
#define  ENUMERATING_LOOP_ACCELERATION_H

#include <goto-programs/goto_program.h>

#include <analyses/natural_loops.h>

#include "loop_acceleration.h"
#include "polynomial_accelerator.h"
#include "path_enumerator.h"
#include "all_paths_enumerator.h"
#include "sat_path_enumerator.h"


class enumerating_loop_accelerationt : public loop_accelerationt {
 public:
  enumerating_loop_accelerationt(
      symbol_tablet &_symbol_table,
      goto_functionst &_goto_functions,
      goto_programt &_goto_program,
      natural_loops_mutablet::natural_loopt &_loop,
      goto_programt::targett _loop_header,
      int _path_limit) :
    symbol_table(_symbol_table),
    goto_functions(_goto_functions),
    goto_program(_goto_program),
    loop(_loop),
    loop_header(_loop_header),
    polynomial_accelerator(symbol_table, goto_functions),
    path_limit(_path_limit)
  {
    //path_enumerator = new all_paths_enumeratort(goto_program, loop, loop_header);
    path_enumerator = new sat_path_enumeratort(symbol_table, goto_functions,
        goto_program, loop, loop_header);
  }

  ~enumerating_loop_accelerationt() {
    delete path_enumerator;
  }

  virtual bool accelerate(path_acceleratort &accelerator);

 protected:
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;
  goto_programt &goto_program;
  natural_loops_mutablet::natural_loopt &loop;
  goto_programt::targett loop_header;
  polynomial_acceleratort polynomial_accelerator;
  int path_limit;

  path_enumeratort *path_enumerator;
};

#endif // ENUMERATING_LOOP_ACCELERATION_H
