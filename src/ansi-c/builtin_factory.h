/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_BUILTIN_FACTORY_H
#define CPROVER_ANSI_C_BUILTIN_FACTORY_H

#include <util/irep.h>

class message_handlert;
class symbol_tablet;

//! \return 'true' in case of error
bool builtin_factory(
  const irep_idt &identifier,
  symbol_tablet &,
  message_handlert &);

#endif // CPROVER_ANSI_C_BUILTIN_FACTORY_H
