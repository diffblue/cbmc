/*******************************************************************\

Module: Symex Shadow Memory Instrumentation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Symex Shadow Memory Instrumentation Utilities

#ifndef CPROVER_GOTO_SYMEX_SHADOW_MEMORY_UTIL_H
#define CPROVER_GOTO_SYMEX_SHADOW_MEMORY_UTIL_H

#include <util/irep.h>

class exprt;

/// Extracts the field name identifier from a string expression,
/// e.g. as passed as argument to a __CPROVER_field_decl_local call.
/// \param string_expr The string argument expression
/// \return The identifier denoted by the string argument expression
irep_idt extract_field_name(const exprt &string_expr);

#endif // CPROVER_GOTO_SYMEX_SHADOW_MEMORY_STATE_H
