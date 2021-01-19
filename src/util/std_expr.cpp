/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "std_expr.h"

#include <util/namespace.h>

#include "arith_tools.h"
#include "byte_operators.h"
#include "c_types.h"
#include "expr_util.h"
#include "mathematical_types.h"
#include "namespace.h"
#include "pointer_offset_size.h"
#include "range.h"
#include "simplify_expr.h"

bool constant_exprt::value_is_zero_string() const
{
  const std::string val=id2string(get_value());
  return val.find_first_not_of('0')==std::string::npos;
}

exprt disjunction(const exprt::operandst &op)
{
  if(op.empty())
    return false_exprt();
  else if(op.size()==1)
    return op.front();
  else
  {
    return or_exprt(exprt::operandst(op));
  }
}

exprt conjunction(const exprt::operandst &op)
{
  if(op.empty())
    return true_exprt();
  else if(op.size()==1)
    return op.front();
  else
  {
    return and_exprt(exprt::operandst(op));
  }
}

// Implementation of struct_exprt::component for const / non const overloads.
template <typename T>
auto component(T &struct_expr, const irep_idt &name, const namespacet &ns)
  -> decltype(struct_expr.op0())
{
  static_assert(
    std::is_base_of<struct_exprt, T>::value, "T must be a struct_exprt.");
  const auto index =
    to_struct_type(ns.follow(struct_expr.type())).component_number(name);
  DATA_INVARIANT(
    index < struct_expr.operands().size(),
    "component matching index should exist");
  return struct_expr.operands()[index];
}

/// \return The expression for a named component of this struct.
exprt &struct_exprt::component(const irep_idt &name, const namespacet &ns)
{
  return ::component(*this, name, ns);
}

/// \return The expression for a named component of this struct.
const exprt &
struct_exprt::component(const irep_idt &name, const namespacet &ns) const
{
  return ::component(*this, name, ns);
}

/// Check that the member expression has the right number of operands, refers
/// to a component that exists on its underlying compound type, and uses the
/// same type as is declared on that compound type. Throws or raises an
/// invariant if not, according to validation mode.
/// \param expr: expression to validate
/// \param ns: global namespace
/// \param vm: validation mode (see \ref exprt::validate)
void member_exprt::validate(
  const exprt &expr,
  const namespacet &ns,
  const validation_modet vm)
{
  check(expr, vm);

  const auto &member_expr = to_member_expr(expr);

  const typet &compound_type = ns.follow(member_expr.compound().type());
  const auto *struct_union_type =
    type_try_dynamic_cast<struct_union_typet>(compound_type);
  DATA_CHECK(
    vm,
    struct_union_type != nullptr,
    "member must address a struct, union or compatible type");

  const auto &component =
    struct_union_type->get_component(member_expr.get_component_name());

  DATA_CHECK(
    vm,
    component.is_not_nil(),
    "member component '" + id2string(member_expr.get_component_name()) +
      "' must exist on addressed type");

  DATA_CHECK(
    vm,
    component.type() == member_expr.type(),
    "member expression's type must match the addressed struct or union "
    "component");
}

void let_exprt::validate(const exprt &expr, const validation_modet vm)
{
  check(expr, vm);

  const auto &let_expr = to_let_expr(expr);

  DATA_CHECK(
    vm,
    let_expr.values().size() == let_expr.variables().size(),
    "number of variables must match number of values");

  for(const auto &binding :
      make_range(let_expr.variables()).zip(let_expr.values()))
  {
    DATA_CHECK(
      vm,
      binding.first.id() == ID_symbol,
      "let binding symbols must be symbols");

    DATA_CHECK(
      vm,
      binding.first.type() == binding.second.type(),
      "let bindings must be type consistent");
  }
}
