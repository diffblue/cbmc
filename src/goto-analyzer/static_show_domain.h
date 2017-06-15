/*******************************************************************\

Module: 

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_GOTO_ANALYZER_STATIC_SHOW_DOMAIN_H
#define CPROVER_GOTO_ANALYZER_STATIC_SHOW_DOMAIN_H

#include <iosfwd>

#include <util/message.h>
#include <util/options.h>

#include <goto-programs/goto_model.h>

bool static_show_domain(
  const goto_modelt &,
  const optionst &,
  message_handlert &,
  std::ostream &);

#endif
