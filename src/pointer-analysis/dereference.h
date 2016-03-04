/*******************************************************************\

Module: Pointer Dereferencing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Dereferencing

#ifndef CPROVER_POINTER_ANALYSIS_DEREFERENCE_H
#define CPROVER_POINTER_ANALYSIS_DEREFERENCE_H

#include <util/expr.h>
#include <util/invariant.h>

class if_exprt;
class namespacet;
class typecast_exprt;

/*! \brief TO_BE_DOCUMENTED
*/
class dereferencet
{
public:
  /*! \brief Constructor
   * \param _ns Namespace
  */
  explicit dereferencet(
    const namespacet &_ns):
    ns(_ns)
  {
  }

  ~dereferencet() { }

  /*!
   * The operator '()' dereferences the
   * given pointer-expression.
   *
   * \param pointer A pointer-typed expression, to
   *        be dereferenced.
   * \param invalid_cond Guarding expression specifying when
   *        dereferencing will yield an invalid object
  */

  exprt operator()(const exprt &pointer, exprt &invalid_cond);

private:
  const namespacet &ns;

  exprt dereference_rec(
    const exprt &address,
    const exprt &offset,
    const typet &type,
    exprt &invalid_cond);

  exprt dereference_if(
    const if_exprt &expr,
    const exprt &offset,
    const typet &type,
    exprt &invalid_cond);

  exprt dereference_plus(
    const exprt &expr,
    const exprt &offset,
    const typet &type,
    exprt &invalid_cond);

  exprt dereference_typecast(
    const typecast_exprt &expr,
    const exprt &offset,
    const typet &type,
    exprt &invalid_cond);

  bool type_compatible(
    const typet &object_type,
    const typet &dereference_type) const;

  exprt read_object(
    const exprt &object,
    const exprt &offset,
    const typet &type);
};

inline exprt dereference(
  const exprt &pointer,
  const namespacet &ns,
  exprt &invalid_cond)
{
  dereferencet dereference_object(ns);
  exprt result=dereference_object(pointer, invalid_cond);
  return result;
}

inline exprt dereference(const exprt &pointer, const namespacet &ns)
{
  exprt invalid_cond;
  exprt result=dereference(pointer, ns, invalid_cond);
  CHECK_RETURN(invalid_cond.is_false());
  return result;
}

#endif // CPROVER_POINTER_ANALYSIS_DEREFERENCE_H
