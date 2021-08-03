/*******************************************************************\

 Module: Variable Sensitivity Domain

 Author: DiffBlue Limited.

\*******************************************************************/

/// \file
/// Represents a stack of write operations to an addressable memory
/// location

#include "write_stack.h"

#include <unordered_set>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>

#include "abstract_environment.h"

/// Build a topstack
write_stackt::write_stackt() : stack(), top_stack(true)
{
}

/// Construct a write stack from an expression
/// \param expr: The expression to represent
/// \param environment: The environment to evaluate any expressions in
/// \param ns: The global namespace
write_stackt::write_stackt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  top_stack = false;
  if(expr.type().id() == ID_array)
  {
    // We are assigning an array to a pointer, which is equivalent to assigning
    // the first element of that array
    // &(expr)[0]
    construct_stack_to_pointer(
      address_of_exprt(index_exprt(expr, from_integer(0, signed_size_type()))),
      environment,
      ns);
  }
  else
  {
    construct_stack_to_pointer(expr, environment, ns);
  }
}

/// Add to the stack the elements to get to a pointer
/// \param expr: An expression of type pointer to construct the stack to
/// \param environment: The environment to evaluate any expressions in
/// \param ns: The global namespace
void write_stackt::construct_stack_to_pointer(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  PRECONDITION(expr.type().id() == ID_pointer);

  if(expr.id() == ID_address_of)
  {
    // resovle reminder, can either be a symbol, member or index of
    // otherwise unsupported
    construct_stack_to_lvalue(
      to_address_of_expr(expr).object(), environment, ns);
  }
  else if(expr.id() == ID_plus || expr.id() == ID_minus)
  {
    exprt base;
    exprt offset;
    const integral_resultt &which_side =
      get_which_side_integral(expr, base, offset);
    INVARIANT(
      which_side != integral_resultt::NEITHER_INTEGRAL,
      "An offset must be an integral amount");

    if(expr.id() == ID_minus)
    {
      // can't get a valid pointer by subtracting from a constant number
      if(which_side == integral_resultt::LHS_INTEGRAL)
      {
        top_stack = true;
        return;
      }
      offset = unary_minus_exprt(offset);
    }

    abstract_object_pointert offset_value = environment.eval(offset, ns);

    add_to_stack(
      std::make_shared<offset_entryt>(offset_value), environment, ns);

    // Build the pointer part
    construct_stack_to_pointer(base, environment, ns);

    if(!top_stack)
    {
      // check the symbol at the bottom of the stack
      std::shared_ptr<const write_stack_entryt> entry = *stack.cbegin();
      INVARIANT(
        entry->get_access_expr().id() == ID_symbol,
        "The base should be an addressable location (i.e. symbol)");

      if(entry->get_access_expr().type().id() != ID_array)
      {
        top_stack = true;
      }
    }
  }
  else
  {
    // unknown expression type - play it safe and set to top
    top_stack = true;
  }
}

/// Construct a stack up to a specific l-value (i.e. symbol or position in an
/// array or struct)
/// \param expr: The expression representing a l-value
/// \param environment: The environment to evaluate any expressions in
/// \param ns: The global namespace
void write_stackt::construct_stack_to_lvalue(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  if(!top_stack)
  {
    if(expr.id() == ID_member)
    {
      add_to_stack(std::make_shared<simple_entryt>(expr), environment, ns);
      construct_stack_to_lvalue(
        to_member_expr(expr).struct_op(), environment, ns);
    }
    else if(expr.id() == ID_symbol || expr.id() == ID_dynamic_object)
    {
      add_to_stack(std::make_shared<simple_entryt>(expr), environment, ns);
    }
    else if(expr.id() == ID_index)
    {
      construct_stack_to_array_index(to_index_expr(expr), environment, ns);
    }
    else
    {
      top_stack = true;
    }
  }
}

/// Construct a stack for an array position l-value.
/// \param index_expr: The index expression to construct to.
/// \param environment: The environment to evaluate any expressions in
/// \param ns: The global namespace
void write_stackt::construct_stack_to_array_index(
  const index_exprt &index_expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  abstract_object_pointert offset_value =
    environment.eval(index_expr.index(), ns);

  add_to_stack(std::make_shared<offset_entryt>(offset_value), environment, ns);
  construct_stack_to_lvalue(index_expr.array(), environment, ns);
}

/// Convert the stack to an expression that can be used to write to.
/// \return The expression representing the stack, with nil_exprt expressions
///   for top elements.
exprt write_stackt::to_expression() const
{
  // A top stack is useless and its expression should not be evaluated
  PRECONDITION(!is_top_value());
  exprt access_expr = nil_exprt();
  for(const std::shared_ptr<write_stack_entryt> &entry : stack)
  {
    exprt new_expr = entry->get_access_expr();
    if(access_expr.id() == ID_nil)
    {
      access_expr = new_expr;
    }
    else
    {
      if(new_expr.operands().size() == 0)
      {
        new_expr.operands().resize(1);
      }
      new_expr.operands()[0] = access_expr;

      // If necessary, complete the type of the new access expression
      entry->adjust_access_type(new_expr);

      access_expr = new_expr;
    }
  }
  address_of_exprt top_expr(access_expr);
  return std::move(top_expr);
}

size_t write_stackt::depth() const
{
  return stack.size();
}

exprt write_stackt::target_expression(size_t depth) const
{
  PRECONDITION(!is_top_value());
  return stack[depth]->get_access_expr();
}

exprt write_stackt::offset_expression() const
{
  PRECONDITION(!is_top_value());
  auto const &access = stack.back()->get_access_expr();

  if(access.id() == ID_member || access.id() == ID_symbol)
    return access;

  if(access.id() == ID_index)
    return to_index_expr(access).index();

  return from_integer(0, unsigned_long_int_type());
}

/// Is the stack representing an unknown value and hence can't be written to
/// or read from.
/// \return True if the stack is top.
bool write_stackt::is_top_value() const
{
  return top_stack;
}

/// Add an element to the top of the stack. This will squash in with the top
/// element if possible.
/// \param entry_pointer: The new element for the stack.
/// \param environment: The environment to evaluate any expressions in
/// \param ns: The global namespace
void write_stackt::add_to_stack(
  std::shared_ptr<write_stack_entryt> entry_pointer,
  const abstract_environmentt environment,
  const namespacet &ns)
{
  if(
    stack.empty() ||
    !stack.front()->try_squash_in(entry_pointer, environment, ns))
  {
    stack.insert(stack.begin(), entry_pointer);
  }
}

/// Utility function to find out which side of a binary operation has an
/// integral type, if any.
/// \param expr: The (binary) expression to evaluate.
/// \param [out] out_base_expr: The sub-expression which is not integral typed
/// \param [out] out_integral_expr: The subexpression which is integraled typed.
/// \return: An enum specifying whether the integral type is the LHS (op0),
///   RHS (op1) or neither.
write_stackt::integral_resultt write_stackt::get_which_side_integral(
  const exprt &expr,
  exprt &out_base_expr,
  exprt &out_integral_expr)
{
  PRECONDITION(expr.operands().size() == 2);
  const auto binary_e = to_binary_expr(expr);
  static const std::unordered_set<irep_idt, irep_id_hash> integral_types = {
    ID_signedbv, ID_unsignedbv, ID_integer};
  if(integral_types.find(binary_e.lhs().type().id()) != integral_types.cend())
  {
    out_integral_expr = binary_e.lhs();
    out_base_expr = binary_e.rhs();
    return integral_resultt::LHS_INTEGRAL;
  }
  else if(
    integral_types.find(binary_e.rhs().type().id()) != integral_types.cend())
  {
    out_integral_expr = binary_e.rhs();
    out_base_expr = binary_e.lhs();
    return integral_resultt::RHS_INTEGRAL;
  }
  else
  {
    out_integral_expr.make_nil();
    out_base_expr.make_nil();
    return integral_resultt::NEITHER_INTEGRAL;
  }
}
