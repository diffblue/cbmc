/*******************************************************************\

Module:

Author: Lucas Cordeiro, lucas.cordeiro@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_GOTO_ANALYZER_STATIC_SIMPLIFIER_H
#define CPROVER_GOTO_ANALYZER_STATIC_SIMPLIFIER_H

#include <iosfwd>

#include <util/message.h>
#include <util/namespace.h>
#include <util/options.h>

#include <goto-programs/goto_model.h>

bool static_simplifier(
  goto_modelt &,
  const optionst &,
  message_handlert &,
  std::ostream &);

#endif
