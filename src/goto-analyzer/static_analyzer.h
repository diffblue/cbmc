/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_GOTO_ANALYZER_STATIC_ANALYZER_H
#define CPROVER_GOTO_ANALYZER_STATIC_ANALYZER_H

#include <iosfwd>

#include <util/message.h>
#include <util/namespace.h>
#include <util/options.h>

#include <goto-programs/goto_model.h>

bool static_analyzer(
  const goto_modelt &,
  const optionst &,
  message_handlert &);

void show_intervals(
  const goto_modelt &,
  std::ostream &);

#endif // CPROVER_GOTO_ANALYZER_STATIC_ANALYZER_H
