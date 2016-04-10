/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_STATIC_ANALYZER_H
#define CPROVER_STATIC_ANALYZER_H

#include <iosfwd>

#include <util/message.h>
#include <util/namespace.h>
#include <util/options.h>

#include <goto-programs/goto_functions.h>

bool static_analyzer(
  const goto_functionst &,
  const namespacet &,
  const optionst &,
  message_handlert &);

void show_intervals(
  const goto_functionst &,
  const namespacet &,
  std::ostream &);

#endif
