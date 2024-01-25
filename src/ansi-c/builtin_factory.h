/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_BUILTIN_FACTORY_H
#define CPROVER_ANSI_C_BUILTIN_FACTORY_H

#include <util/irep.h>

class message_handlert;
class symbol_table_baset;

//! \return 'true' in case of error
bool builtin_factory(
  const irep_idt &identifier,
  bool support_float16_type,
  symbol_table_baset &,
  message_handlert &);

#endif // CPROVER_ANSI_C_BUILTIN_FACTORY_H
