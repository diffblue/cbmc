/*******************************************************************\

Module: Library Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Library Linking

#ifndef CPROVER_GOTO_PROGRAMS_LINK_TO_LIBRARY_H
#define CPROVER_GOTO_PROGRAMS_LINK_TO_LIBRARY_H

#include <util/irep.h>

#include <functional>
#include <set>

class goto_modelt;
class message_handlert;
class symbol_tablet;

void link_to_library(
  goto_modelt &,
  message_handlert &,
  const std::function<void(
    const std::set<irep_idt> &,
    const symbol_tablet &,
    symbol_tablet &,
    message_handlert &)> &);

#endif // CPROVER_GOTO_PROGRAMS_LINK_TO_LIBRARY_H
