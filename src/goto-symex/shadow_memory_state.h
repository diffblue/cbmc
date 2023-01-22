/*******************************************************************\

Module: Symex Shadow Memory Instrumentation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Symex Shadow Memory Instrumentation State

#ifndef CPROVER_GOTO_SYMEX_SHADOW_MEMORY_STATE_H
#define CPROVER_GOTO_SYMEX_SHADOW_MEMORY_STATE_H

#include <util/std_expr.h>

#include "shadow_memory_field_definitions.h"

#include <map>

class address_of_exprt;

/// \brief The state maintained by the shadow memory instrumentation
/// during symbolic execution.
class shadow_memory_statet
{
public:
  /// The available shadow memory field definitions
  shadow_memory_field_definitionst fields;

  struct shadowed_addresst
  {
    exprt address;
    symbol_exprt shadow;
  };

  // addresses must remain in sequence
  std::map<irep_idt, std::vector<shadowed_addresst>> address_fields;
};

#endif // CPROVER_GOTO_SYMEX_SHADOW_MEMORY_STATE_H
