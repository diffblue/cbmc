/*******************************************************************\

Module: Pointer Dereferencing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Dereferencing

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_DEREFERENCE_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_DEREFERENCE_H

#include <unordered_set>

#include <util/std_expr.h>

#include "dereference_callback.h"

class symbol_tablet;
class optionst;
class symbolt;

/// Wrapper for a function dereferencing pointer expressions using a value set.
class value_set_dereferencet final
{
public:
  /// \param _ns: Namespace
  /// \param _new_symbol_table: A symbol_table to store new symbols in
  /// \param _dereference_callback: Callback object for getting the set of
  ///   objects a given pointer may point to.
  /// \param _language_mode: Mode for any new symbols created to represent a
  ///   dereference failure
  /// \param _exclude_null_derefs: Ignore value-set entries that indicate a
  //    given dereference may follow a null pointer
  value_set_dereferencet(
    const namespacet &_ns,
    symbol_tablet &_new_symbol_table,
    dereference_callbackt &_dereference_callback,
    const irep_idt _language_mode,
    bool _exclude_null_derefs):
    ns(_ns),
    new_symbol_table(_new_symbol_table),
    dereference_callback(_dereference_callback),
    language_mode(_language_mode),
    exclude_null_derefs(_exclude_null_derefs)
  { }

  virtual ~value_set_dereferencet() { }

  /// Dereference the given pointer-expression. Any errors are
  /// reported to the callback method given in the constructor.
  /// \param pointer: A pointer-typed expression, to be dereferenced.
  exprt dereference(const exprt &pointer);

  /// Return value for `build_reference_to`; see that method for documentation.
  class valuet
  {
  public:
    exprt value;
    exprt pointer;
    exprt pointer_guard;

    valuet()
      : value{nil_exprt{}}, pointer{nil_exprt{}}, pointer_guard{false_exprt{}}
    {
    }
  };

  static bool should_ignore_value(
    const exprt &what,
    bool exclude_null_derefs,
    const irep_idt &language_mode);

  static valuet build_reference_to(
    const exprt &what,
    const exprt &pointer,
    const namespacet &ns);

  static bool dereference_type_compare(
    const typet &object_type,
    const typet &dereference_type,
    const namespacet &ns);

  static bool memory_model(
    exprt &value,
    const typet &type,
    const exprt &offset,
    const namespacet &ns);

  static bool memory_model_bytes(
    exprt &value,
    const typet &type,
    const exprt &offset,
    const namespacet &ns);

private:
  const namespacet &ns;
  symbol_tablet &new_symbol_table;
  dereference_callbackt &dereference_callback;
  /// language_mode: ID_java, ID_C or another language identifier
  /// if we know the source language in use, irep_idt() otherwise.
  const irep_idt language_mode;
  /// Flag indicating whether `value_set_dereferencet::dereference` should
  /// disregard an apparent attempt to dereference NULL
  const bool exclude_null_derefs;
};

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_DEREFERENCE_H
