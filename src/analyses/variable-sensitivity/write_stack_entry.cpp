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
/// \return The expression to read this part of the stack
exprt simple_entryt::get_access_expr() const
{
  return simple_entry;
}

/// For a simple entry, no type adjustment is needed for the access expression
void simple_entryt::adjust_access_type(exprt &expr) const
{
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
/// this is an index expression with the index() part the offset.
/// It is important to note that the returned index_exprt does not have a type,
/// so it will be necessary for the caller to update the type whenever the index
/// expression is completed using `adjust_access_type` on the resulting exprt.
/// \return The untyped expression to read this part of the stack
exprt offset_entryt::get_access_expr() const
{
  // This constructs a something that is basicallyt '(null)[offset])'
  // meaning that we don't know what the type is at this point, as the
  // array part will be filled in later.
  return index_exprt(nil_exprt(), offset->to_constant());
}

/// For an offset entry, the type of the access expression can only be
/// determined once the access expression has been completed with the next
/// entry on the write stack.
void offset_entryt::adjust_access_type(exprt &expr) const
{
  PRECONDITION(expr.id() == ID_index);
  expr.type() = to_index_expr(expr).array().type().subtype();
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
