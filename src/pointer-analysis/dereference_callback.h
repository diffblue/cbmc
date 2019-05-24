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

  DEPRECATED(SINCE(2019, 05, 22, "use vector returning version instead"))
  virtual void
  get_value_set(const exprt &expr, value_setst::valuest &value_set) const = 0;

  virtual std::vector<exprt> get_value_set(const exprt &expr) const = 0;

  virtual const symbolt *get_or_create_failed_symbol(const exprt &expr) = 0;
};

#endif // CPROVER_POINTER_ANALYSIS_DEREFERENCE_CALLBACK_H
