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

  /// Descriptor for the possible values to may be reached by dereferencing
  /// a pointer
  struct value_set_resultt
  {
    /// Pointer expression that produced this value-set
    exprt pointer;
    /// Set of values that may result from dereferencing pointer_expr
    std::vector<valuet> values;
    /// Can dereferencing pointer_expr fail (for example, could it be null,
    /// or could it point to unallocated memory)?
    bool may_fail;
  };

  /// Mapping from a placeholder symbol to a value-set. These are created by
  /// gather_value_sets, which replaces expressions to be dereferenced with
  /// placeholder symbols and records the corresponding value set an instance
  /// of this struct.
  struct value_set_mappingt
  {
    /// Placeholder symbol corresponding to this value-set
    symbol_exprt placeholder;
    /// Value-set
    value_set_resultt values;
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

  /// Find the subexpressions of \p pointer that can be independently
  /// dereferenced, replace each one with a placeholder symbol, and accumulate
  /// the mapping from placeholders to value-sets in \p value_set_accumulator.
  /// For example, if \p pointer was 'x ? y : z' then we might independently
  /// dereference 'y' and 'z' and return `x ? placeholder1 : placeholder2`, with
  /// value_set_accumulator containing "placeholder1 -> y, {a, b}" and
  /// "placeholder2 -> z, {c, d}", where y and z are the original pointers and
  /// {a, b, c, d} possible objects the pointer subexpressions may point to.
  /// Note in the simplest case this will just return "placeholder1" and
  /// populate \p value_set_accumulator with a single entry.
  exprt gather_value_sets(
    const exprt &pointer,
    std::vector<value_set_mappingt> &value_set_accumulator) const;

  /// Find the objects that \p pointer may point to. The result is effectively a
  /// tuple, <pointer, value-set, may-fail>, where may-fail indicates whether
  /// pointer may point to anything other than an allocated object, such as an
  /// integer cast to a pointer or a null pointer.
  value_set_resultt get_value_set(const exprt &pointer) const;

  /// Converts a value-set into a conditional expression -- for example, if the
  /// input \p value_set has values {a, b, c} we might return
  /// `(p == &a ? a : p == &b ? b : c)`, where `p` is the dereferenced pointer
  /// given in `value_set.pointer`. If `value_set.may_fail` is set then the
  /// result expression will contain a fall-back catch-all symbol, such as
  /// `p == &o1 ? o1 : symex::invalid_object$1`
  exprt value_set_to_conditional_expr(const value_set_resultt &value_set) const;
};

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_DEREFERENCE_H
