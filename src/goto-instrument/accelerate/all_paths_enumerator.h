/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_ALL_PATHS_ENUMERATOR_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_ALL_PATHS_ENUMERATOR_H

#include <goto-programs/goto_program.h>

#include <analyses/natural_loops.h>

#include "path.h"
#include "path_enumerator.h"

class all_paths_enumeratort:public path_enumeratort
{
public:
  all_paths_enumeratort(
    goto_programt &_goto_program,
    natural_loops_mutablet::natural_loopt &_loop,
    goto_programt::targett _loop_header):
    goto_program(_goto_program),
    loop(_loop),
    loop_header(_loop_header)
  {
  }

  virtual bool next(patht &path);

protected:
  std::size_t backtrack(patht &path);
  void complete_path(patht &path, std::size_t succ);
  void extend_path(patht &path, goto_programt::targett t, std::size_t succ);
  bool is_looping(patht &path);

  goto_programt &goto_program;
  natural_loops_mutablet::natural_loopt &loop;
  goto_programt::targett loop_header;

  patht last_path;
};

#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_ALL_PATHS_ENUMERATOR_H
