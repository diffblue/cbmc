/*******************************************************************\

Module: API for Language Frontends

Author: Daniel Kroening

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_FRONTEND_H
#define CPROVER_GOTO_PROGRAMS_GOTO_FRONTEND_H

#include <util/symbol.h>

#include "goto_function.h"

/// Abstract interface for language frontends
class goto_frontendt
{
public:
  virtual ~goto_frontendt();

  /// Construct a GOTO function by name,
  /// or throws if this is not possible.
  /// \return rvalue for function body
  virtual const goto_functiont &&make_function(const irep_idt &) = 0;

  /// Get a symbol by name, or throws if the symbol does not exist.
  virtual const symbolt &get_symbol(const irep_idt &) = 0;

  /// Get an identifier of a function that is the
  /// designated entry point.
  virtual irep_idt entry_point() const;
};

#endif
