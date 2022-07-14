/*******************************************************************\

 Module: Analyses Variable Sensitivity

 Author: DiffBlue Limited.

\*******************************************************************/

/// \file
/// Represents an entry in the write_stackt

#include <unordered_set>

#include "abstract_environment.h"
#include "write_stack_entry.h"

/// Try to combine a new stack element with the current top of the stack
/// \param new_entry: The new entry to combine with
/// \param enviroment: The enviroment to evalaute things in
/// \param ns: The global namespace
/// \return True if this stack entry and thew new entry were combined
bool write_stack_entryt::try_squash_in(
  std::shared_ptr<const write_stack_entryt> new_entry,
  const abstract_environmentt &enviroment,
  const namespacet &ns)
{
  return false;
}

/// Build a simple entry based off a single expression
/// \param expr: The expression being represented
simple_entryt::simple_entryt(exprt expr) : simple_entry(expr)
{
  // Invalid simple expression added to the stack
  PRECONDITION(
    expr.id() == ID_member || expr.id() == ID_symbol ||
    expr.id() == ID_dynamic_object);
}

/// Get the expression part needed to read this stack entry. For simple
/// expressions this is just the expression itself.
/// \return The expression to read this part of the stack and false
std::pair<exprt, bool> simple_entryt::get_access_expr() const
{
  return {simple_entry, false};
}

offset_entryt::offset_entryt(abstract_object_pointert offset_value)
  : offset(offset_value)
{
  // The type of the abstract object should be an integral number
  static const std::unordered_set<irep_idt, irep_id_hash> integral_types = {
    ID_signedbv, ID_unsignedbv, ID_integer};
  PRECONDITION(
    integral_types.find(offset_value->type().id()) != integral_types.cend());
}

/// Get the expression part needed to read this stack entry. For offset entries
/// this is the offset for an index expression.
/// \return The offset expression to read this part of the stack and true
std::pair<exprt, bool> offset_entryt::get_access_expr() const
{
  return {offset->to_constant(), true};
}

/// Try to combine a new stack element with the current top of the stack. This
/// will succeed if they are both offsets as we can combine these offsets into
/// the sum of the offsets
/// \param new_entry: The new entry to combine with
/// \param enviroment: The enviroment to evalaute things in
/// \param ns: The global namespace
/// \return True if this stack entry and thew new entry were combined
bool offset_entryt::try_squash_in(
  std::shared_ptr<const write_stack_entryt> new_entry,
  const abstract_environmentt &enviroment,
  const namespacet &ns)
{
  std::shared_ptr<const offset_entryt> cast_entry =
    std::dynamic_pointer_cast<const offset_entryt>(new_entry);
  if(cast_entry)
  {
    plus_exprt result_offset(
      cast_entry->offset->to_constant(), offset->to_constant());
    offset = enviroment.eval(result_offset, ns);
    return true;
  }
  return false;
}
