/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_PATH_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_PATH_H

#include <iosfwd>
#include <list>

#include <util/std_expr.h>
#include <util/namespace.h>

#include <goto-programs/goto_program.h>

class path_nodet
{
public:
  explicit path_nodet(const goto_programt::targett &_loc):
    loc(_loc),
    guard(nil_exprt())
  {
  }

  path_nodet(const goto_programt::targett &_loc,
             const exprt &_guard) :
      loc(_loc),
      guard(_guard)
  {
  }

  void output(const goto_programt &program, std::ostream &str) const;

  goto_programt::targett loc;
  const exprt guard;
};

using patht = std::list<path_nodet>;
using pathst = std::list<patht>;

void output_path(
  const patht &path,
  const goto_programt &program,
  const namespacet &ns,
  std::ostream &str);

#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_PATH_H
