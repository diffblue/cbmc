/*******************************************************************\

Module: Pointer Dereferencing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Dereferencing

#ifndef CPROVER_POINTER_ANALYSIS_DEREFERENCE_CALLBACK_H
#define CPROVER_POINTER_ANALYSIS_DEREFERENCE_CALLBACK_H

#include <string>

#include "value_sets.h"

class exprt;
class symbolt;

/// Base class for pointer value set analysis.
/// Implemented by goto_program_dereferencet.
/// This exists so that `value_set_dereferencet` can contain a reference to
/// `goto_program_derefencet` which cannot be done directly because
/// `goto_program_derefencet` contains a `value_set_dereferencet`.
class dereference_callbackt
{
public:
  virtual ~dereference_callbackt() = default;

  virtual std::vector<exprt> get_value_set(const exprt &expr) const = 0;

  virtual const symbolt *get_or_create_failed_symbol(const exprt &expr) = 0;

  /// Get the L1-renamed (SSA, without constant propagation) version of a
  /// symbol expression. Used by the wide pointer encoding's address-based
  /// dereference dispatch to read from the correct object instance. L1 rather
  /// than L2 is required: L2 would substitute the symbol with its current
  /// value, causing width mismatches in the subsequent `byte_extract`.
  /// Default implementation returns the expression unchanged.
  virtual exprt get_renamed_symbol(const exprt &expr) const
  {
    return expr;
  }
};

#endif // CPROVER_POINTER_ANALYSIS_DEREFERENCE_CALLBACK_H
