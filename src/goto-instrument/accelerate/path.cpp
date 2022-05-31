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
  std::ostream &str)
{
  for(const auto &step : path)
    step.loc->output(str);
}
