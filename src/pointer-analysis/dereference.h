/*******************************************************************\

Module: Pointer Dereferencing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Dereferencing

#ifndef CPROVER_POINTER_ANALYSIS_DEREFERENCE_H
#define CPROVER_POINTER_ANALYSIS_DEREFERENCE_H

#include <util/namespace.h>
#include <util/expr.h>

class if_exprt;
class typecast_exprt;

/// Wrapper for a function which dereference a pointer-expression.
class dereferencet
{
public:
  /// \param _ns: Namespace
  explicit dereferencet(
    const namespacet &_ns):
    ns(_ns)
  {
  }

  ~dereferencet() { }

  /// Dereference the given pointer-expression.
  /// \param pointer: A pointer-typed expression, to be dereferenced.
  /// \return Object after dereferencing.
  exprt operator()(const exprt &pointer);

private:
  const namespacet &ns;

  exprt dereference_rec(
    const exprt &address,
    const exprt &offset,
    const typet &type);

  exprt dereference_if(
    const if_exprt &expr,
    const exprt &offset,
    const typet &type);

  exprt dereference_plus(
    const exprt &expr,
    const exprt &offset,
    const typet &type);

  exprt dereference_typecast(
    const typecast_exprt &expr,
    const exprt &offset,
    const typet &type);

  bool type_compatible(
    const typet &object_type,
    const typet &dereference_type) const;

  exprt read_object(
    const exprt &object,
    const exprt &offset,
    const typet &type);
};

/// Dereference the given pointer-expression.
/// \param pointer: A pointer-typed expression, to be dereferenced.
/// \param ns: namespace
/// \return Object after dereferencing.
inline exprt dereference(const exprt &pointer, const namespacet &ns)
{
  dereferencet dereference_object(ns);
  return dereference_object(pointer);
}

#endif // CPROVER_POINTER_ANALYSIS_DEREFERENCE_H
