/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#include "path.h"

#include <goto-programs/goto_program.h>

void output_path(
  const patht &path,
  const goto_programt &program,
  const namespacet &ns,
  std::ostream &str)
{
  for(const auto &step : path)
    program.output_instruction(ns, "path", str, *step.loc);
}
