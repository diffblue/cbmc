/*******************************************************************\

Module: 

Author: Lucas Cordeiro, lucas.cordeiro@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_STATIC_SIMPLIFIER_H
#define CPROVER_STATIC_SIMPLIFIER_H

#include <iosfwd>

#include <util/message.h>
#include <util/namespace.h>
#include <util/options.h>

#include <goto-programs/goto_model.h>

bool static_simplifier(
  const goto_modelt &,
  const optionst &,
  message_handlert &);

#endif
