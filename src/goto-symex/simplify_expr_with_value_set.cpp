/*******************************************************************\

Module: Variant of simplify_exprt that uses a value_sett

Author: Michael Tautschnig

\*******************************************************************/

#include "simplify_expr_with_value_set.h"

#include <util/expr_util.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/ssa_expr.h>

#include <pointer-analysis/add_failed_symbols.h>
#include <pointer-analysis/value_set.h>
#include <pointer-analysis/value_set_dereference.h>

#include "goto_symex_can_forward_propagate.h"

/// Try to evaluate a simple pointer comparison.
/// \param operation: ID_equal or ID_not_equal
/// \param symbol_expr: The symbol expression in the condition
/// \param other_operand: The other expression in the condition; we only support
///   an address of expression, a typecast of an address of expression or a
///   null pointer, and return an empty std::optional in all other cases
/// \param value_set: The value-set for looking up what the symbol can point to
/// \param language_mode: The language mode
/// \param ns: A namespace
/// \return If we were able to evaluate the condition as true or false then we
///   return that, otherwise we return an empty std::optional
static std::optional<exprt> try_evaluate_pointer_comparison(
  const irep_idt &operation,
  const symbol_exprt &symbol_expr,
  const exprt &other_operand,
  const value_sett &value_set,
  const irep_idt language_mode,
  const namespacet &ns)
{
  const constant_exprt *constant_expr =
    expr_try_dynamic_cast<constant_exprt>(other_operand);

  if(
    skip_typecast(other_operand).id() != ID_address_of &&
    (!constant_expr || !constant_expr->is_null_pointer()))
  {
    return {};
  }

  const ssa_exprt *ssa_symbol_expr =
    expr_try_dynamic_cast<ssa_exprt>(symbol_expr);

  ssa_exprt l1_expr{*ssa_symbol_expr};
  l1_expr.remove_level_2();
  const std::vector<exprt> value_set_elements =
    value_set.get_value_set(l1_expr, ns);

  bool constant_found = false;

  for(const auto &value_set_element : value_set_elements)
  {
    if(
      value_set_element.id() == ID_unknown ||
      value_set_element.id() == ID_invalid ||
      is_failed_symbol(
        to_object_descriptor_expr(value_set_element).root_object()) ||
      to_object_descriptor_expr(value_set_element).offset().id() == ID_unknown)
    {
      // We can't conclude anything about the value-set
      return {};
    }

    if(!constant_found)
    {
      if(value_set_dereferencet::should_ignore_value(
           value_set_element, false, language_mode))
      {
        continue;
      }

      value_set_dereferencet::valuet value =
        value_set_dereferencet::build_reference_to(
          value_set_element, symbol_expr, ns);

      // use the simplifier to test equality as we need to skip over typecasts
      // and cannot rely on canonical representations, which would permit a
      // simple syntactic equality test
      exprt test_equal = simplify_expr(
        equal_exprt{
          typecast_exprt::conditional_cast(value.pointer, other_operand.type()),
          other_operand},
        ns);
      if(test_equal.is_true())
      {
        constant_found = true;
        // We can't break because we have to make sure we find any instances of
        // ID_unknown or ID_invalid
      }
      else if(!test_equal.is_false())
      {
        // We can't conclude anything about the value-set
        return {};
      }
    }
  }

  if(!constant_found)
  {
    // The symbol cannot possibly have the value \p other_operand because it
    // isn't in the symbol's value-set
    return operation == ID_equal ? static_cast<exprt>(false_exprt{})
                                 : static_cast<exprt>(true_exprt{});
  }
  else if(value_set_elements.size() == 1)
  {
    // The symbol must have the value \p other_operand because it is the only
    // thing in the symbol's value-set
    return operation == ID_equal ? static_cast<exprt>(true_exprt{})
                                 : static_cast<exprt>(false_exprt{});
  }
  else
  {
    return {};
  }
}

simplify_exprt::resultt<> simplify_expr_with_value_sett::simplify_inequality(
  const binary_relation_exprt &expr)
{
  if(expr.id() != ID_equal && expr.id() != ID_notequal)
    return simplify_exprt::simplify_inequality(expr);

  if(!can_cast_type<pointer_typet>(to_binary_expr(expr).op0().type()))
    return simplify_exprt::simplify_inequality(expr);

  exprt lhs = to_binary_expr(expr).op0(), rhs = to_binary_expr(expr).op1();
  if(can_cast_expr<symbol_exprt>(rhs))
    std::swap(lhs, rhs);

  const symbol_exprt *symbol_expr_lhs =
    expr_try_dynamic_cast<symbol_exprt>(lhs);

  if(!symbol_expr_lhs)
    return simplify_exprt::simplify_inequality(expr);

  if(!goto_symex_can_forward_propagatet(ns)(rhs))
    return simplify_exprt::simplify_inequality(expr);

  auto maybe_constant = try_evaluate_pointer_comparison(
    expr.id(), *symbol_expr_lhs, rhs, value_set, language_mode, ns);
  if(maybe_constant.has_value())
    return changed(*maybe_constant);
  else
    return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_expr_with_value_sett::simplify_inequality_pointer_object(
  const binary_relation_exprt &expr)
{
  PRECONDITION(expr.id() == ID_equal || expr.id() == ID_notequal);
  PRECONDITION(expr.is_boolean());

  auto collect_objects = [this](const exprt &pointer)
  {
    std::set<exprt> objects;
    if(auto address_of = expr_try_dynamic_cast<address_of_exprt>(pointer))
    {
      objects.insert(
        object_descriptor_exprt::root_object(address_of->object()));
    }
    else if(auto ssa_expr = expr_try_dynamic_cast<ssa_exprt>(pointer))
    {
      ssa_exprt l1_expr{*ssa_expr};
      l1_expr.remove_level_2();
      const std::vector<exprt> value_set_elements =
        value_set.get_value_set(l1_expr, ns);

      for(const auto &value_set_element : value_set_elements)
      {
        if(
          value_set_element.id() == ID_unknown ||
          value_set_element.id() == ID_invalid ||
          is_failed_symbol(
            to_object_descriptor_expr(value_set_element).root_object()))
        {
          objects.clear();
          break;
        }

        objects.insert(
          to_object_descriptor_expr(value_set_element).root_object());
      }
    }
    return objects;
  };

  auto lhs_objects =
    collect_objects(to_pointer_object_expr(expr.lhs()).pointer());
  auto rhs_objects =
    collect_objects(to_pointer_object_expr(expr.rhs()).pointer());

  if(lhs_objects.size() == 1 && lhs_objects == rhs_objects)
  {
    // there is exactly one pointed-to object on both left-hand and right-hand
    // side, and that object is the same
    return expr.id() == ID_equal ? changed(static_cast<exprt>(true_exprt{}))
                                 : changed(static_cast<exprt>(false_exprt{}));
  }

  std::list<exprt> intersection;
  std::set_intersection(
    lhs_objects.begin(),
    lhs_objects.end(),
    rhs_objects.begin(),
    rhs_objects.end(),
    std::back_inserter(intersection));
  if(!lhs_objects.empty() && !rhs_objects.empty() && intersection.empty())
  {
    // all pointed-to objects on the left-hand side are different from any of
    // the pointed-to objects on the right-hand side
    return expr.id() == ID_equal ? changed(static_cast<exprt>(false_exprt{}))
                                 : changed(static_cast<exprt>(true_exprt{}));
  }

  return simplify_exprt::simplify_inequality_pointer_object(expr);
}

simplify_exprt::resultt<>
simplify_expr_with_value_sett::simplify_pointer_offset(
  const pointer_offset_exprt &expr)
{
  const exprt &ptr = expr.pointer();

  if(ptr.type().id() != ID_pointer)
    return unchanged(expr);

  const ssa_exprt *ssa_symbol_expr = expr_try_dynamic_cast<ssa_exprt>(ptr);

  if(!ssa_symbol_expr)
    return simplify_exprt::simplify_pointer_offset(expr);

  ssa_exprt l1_expr{*ssa_symbol_expr};
  l1_expr.remove_level_2();
  const std::vector<exprt> value_set_elements =
    value_set.get_value_set(l1_expr, ns);

  std::optional<exprt> offset;

  for(const auto &value_set_element : value_set_elements)
  {
    if(
      value_set_element.id() == ID_unknown ||
      value_set_element.id() == ID_invalid ||
      is_failed_symbol(
        to_object_descriptor_expr(value_set_element).root_object()) ||
      to_object_descriptor_expr(value_set_element).offset().id() == ID_unknown)
    {
      offset.reset();
      break;
    }

    exprt this_offset = to_object_descriptor_expr(value_set_element).offset();
    if(
      this_offset.id() == ID_unknown ||
      (offset.has_value() && this_offset != *offset))
    {
      offset.reset();
      break;
    }
    else if(!offset.has_value())
    {
      offset = this_offset;
    }
  }

  if(!offset.has_value())
    return simplify_exprt::simplify_pointer_offset(expr);

  return changed(
    simplify_rec(typecast_exprt::conditional_cast(*offset, expr.type())));
}
