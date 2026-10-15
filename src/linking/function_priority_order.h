/*******************************************************************\

Module: Ordering of constructor/destructor functions by GCC priority

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Ordering of constructor/destructor functions by their GCC priority
/// attribute

#ifndef CPROVER_LINKING_FUNCTION_PRIORITY_ORDER_H
#define CPROVER_LINKING_FUNCTION_PRIORITY_ORDER_H

#include <util/mp_arith.h>

#include <functional>
#include <list>
#include <optional>
#include <utility>

class symbolt;

/// Direction in which constructor/destructor functions are ordered by priority.
enum class function_priority_ordert
{
  /// Ascending priority, with unprioritised functions last. This is the order
  /// in which GCC runs constructors.
  ASCENDING,
  /// Descending priority, with unprioritised functions first. This is the order
  /// in which GCC runs destructors (the reverse of constructors).
  DESCENDING
};

/// Order constructor/destructor functions by their GCC priority attribute.
///
/// GCC runs constructors in ascending priority order with the unprioritised
/// ones last, and destructors in the exact reverse (unprioritised first, then
/// descending priority). See
/// https://gcc.gnu.org/onlinedocs/gcc/Common-Function-Attributes.html.
///
/// \param functions: (symbol, optional priority) pairs in source order; the
///   relative order of functions sharing a priority (and of unprioritised
///   functions) is preserved.
/// \param order: ASCENDING for constructors, DESCENDING for destructors.
/// \return the symbols in the order their calls should be emitted.
std::list<std::reference_wrapper<const symbolt>> order_functions_by_priority(
  const std::list<
    std::pair<std::reference_wrapper<const symbolt>, std::optional<mp_integer>>>
    &functions,
  function_priority_ordert order);

#endif // CPROVER_LINKING_FUNCTION_PRIORITY_ORDER_H
