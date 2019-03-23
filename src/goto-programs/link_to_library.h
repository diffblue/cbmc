/*******************************************************************\

Module: Library Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Library Linking

#ifndef CPROVER_GOTO_PROGRAMS_LINK_TO_LIBRARY_H
#define CPROVER_GOTO_PROGRAMS_LINK_TO_LIBRARY_H

#include <functional>
#include <set>

#include <util/deprecate.h>
#include <util/irep.h>

class goto_functionst;
class goto_modelt;
class message_handlert;
class symbol_tablet;

DEPRECATED(SINCE(2019, 2, 28, "Use link_to_library(goto_model, ...) instead"))
void link_to_library(
  symbol_tablet &,
  goto_functionst &,
  message_handlert &,
  const std::function<
    void(const std::set<irep_idt> &, symbol_tablet &, message_handlert &)> &);

void link_to_library(
  goto_modelt &,
  message_handlert &,
  const std::function<
    void(const std::set<irep_idt> &, symbol_tablet &, message_handlert &)> &);

#endif // CPROVER_GOTO_PROGRAMS_LINK_TO_LIBRARY_H
