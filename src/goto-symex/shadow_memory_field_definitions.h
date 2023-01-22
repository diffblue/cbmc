/*******************************************************************\

Module: Symex Shadow Memory Instrumentation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Symex Shadow Memory Field Definitions

#ifndef CPROVER_GOTO_SYMEX_SHADOW_MEMORY_FIELD_DEFINITIONS_H
#define CPROVER_GOTO_SYMEX_SHADOW_MEMORY_FIELD_DEFINITIONS_H

#include <util/expr.h>

#include <map>

/// \brief The shadow memory field definitions
class shadow_memory_field_definitionst
{
public:
  /// A field definition mapping a field name to its initial value
  using field_definitiont = std::map<irep_idt, exprt>;

  /// Field definitions for global-scope fields
  field_definitiont global_fields;

  /// Field definitions for local-scope fields
  field_definitiont local_fields;
};

#endif // CPROVER_GOTO_SYMEX_SHADOW_MEMORY_FIELD_DEFINITIONS_H
