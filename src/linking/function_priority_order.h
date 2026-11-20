/*******************************************************************\

Module: Ordering of constructor/destructor functions by GCC priority

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Ordering of constructor/destructor functions by their GCC priority
/// attribute

#ifndef CPROVER_LINKING_FUNCTION_PRIORITY_ORDER_H
#define CPROVER_LINKING_FUNCTION_PRIORITY_ORDER_H

#include <util/mp_arith.h>

#include <functional>
#include <vector>

class symbolt;

/// Direction in which constructor/destructor functions are ordered by priority.
enum class function_priority_ordert
{
  /// Ascending priority. This is the order in which GCC runs constructors.
  ASCENDING,
  /// The exact reverse of ASCENDING. This is the order in which GCC runs
  /// destructors.
  DESCENDING
};

/// The priority of a function without an explicit priority:
/// `__attribute__((constructor))` is the same as
/// `__attribute__((constructor(65535)))`, and likewise for destructors.
#define DEFAULT_FUNCTION_PRIORITY 65535

/// The priority of the constructor or destructor function \p symbol: the
/// type-checked argument of its `constructor`/`destructor` attribute, or
/// DEFAULT_FUNCTION_PRIORITY.
mp_integer function_priority(const symbolt &symbol);

/// Order constructor/destructor functions by their GCC priority attribute
/// (https://gcc.gnu.org/onlinedocs/gcc/Common-Function-Attributes.html).
///
/// GCC runs constructors in ascending priority order, and destructors in the
/// exact reverse of that order. Functions without an explicit priority have
/// priority DEFAULT_FUNCTION_PRIORITY. GCC orders functions of equal priority
/// by their position in the program, which CBMC does not record: here,
/// constructors of equal priority keep the order of \p functions, and the
/// order of destructors is the exact reverse of that.
///
/// \param functions: the constructor or destructor functions
/// \param order: ASCENDING for constructors, DESCENDING for destructors.
/// \return the symbols in the order their calls should be emitted.
std::vector<std::reference_wrapper<const symbolt>> order_functions_by_priority(
  const std::vector<std::reference_wrapper<const symbolt>> &functions,
  function_priority_ordert order);

#endif // CPROVER_LINKING_FUNCTION_PRIORITY_ORDER_H
