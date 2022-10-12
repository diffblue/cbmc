/*******************************************************************\

Module: Checks for Errors in C/C++ Programs

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Checks for Errors in C/C++ Programs

#include "c_safety_checks.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>

#include <goto-programs/goto_model.h>

#include <ansi-c/expr2c.h>

exprt index_array_size(const typet &type)
{
  if(type.id() == ID_array)
    return to_array_type(type).size();
  else if(type.id() == ID_vector)
    return to_vector_type(type).size();
  else
    PRECONDITION(false);
}

enum class access_typet
{
  R,
  W
};

void c_safety_checks_rec(
  goto_functionst::function_mapt::value_type &,
  const exprt::operandst &guards,
  const exprt &,
  access_typet,
  const namespacet &,
  goto_programt &);

void c_safety_checks_address_rec(
  goto_functionst::function_mapt::value_type &f,
  const exprt::operandst &guards,
  const exprt &expr,
  const namespacet &ns,
  goto_programt &dest)
{
  if(expr.id() == ID_index)
  {
    const auto &index_expr = to_index_expr(expr);
    c_safety_checks_address_rec(f, guards, index_expr.array(), ns, dest);
    c_safety_checks_rec(
      f, guards, index_expr.index(), access_typet::R, ns, dest);
  }
  else if(expr.id() == ID_member)
  {
    c_safety_checks_address_rec(
      f, guards, to_member_expr(expr).struct_op(), ns, dest);
  }
}

static exprt guard(const exprt::operandst &guards, exprt cond)
{
  if(guards.empty())
    return cond;
  else
    return implies_exprt(conjunction(guards), std::move(cond));
}

void c_safety_checks_rec(
  goto_functionst::function_mapt::value_type &f,
  const exprt::operandst &guards,
  const exprt &expr,
  access_typet access_type,
  const namespacet &ns,
  goto_programt &dest)
{
  if(expr.id() == ID_address_of)
  {
    c_safety_checks_address_rec(
      f, guards, to_address_of_expr(expr).object(), ns, dest);
    return;
  }
  else if(expr.id() == ID_and)
  {
    auto new_guards = guards;
    for(auto &op : expr.operands())
    {
      c_safety_checks_rec(
        f, new_guards, op, access_type, ns, dest); // rec. call
      new_guards.push_back(op);
    }
    return;
  }
  else if(expr.id() == ID_or)
  {
    auto new_guards = guards;
    for(auto &op : expr.operands())
    {
      c_safety_checks_rec(
        f, new_guards, op, access_type, ns, dest); // rec. call
      new_guards.push_back(not_exprt(op));
    }
    return;
  }
  else if(expr.id() == ID_if)
  {
    const auto &if_expr = to_if_expr(expr);
    c_safety_checks_rec(
      f, guards, if_expr.cond(), access_typet::R, ns, dest); // rec. call
    auto new_guards = guards;
    new_guards.push_back(if_expr.cond());
    c_safety_checks_rec(
      f, new_guards, if_expr.true_case(), access_type, ns, dest); // rec. call
    new_guards.pop_back();
    new_guards.push_back(not_exprt(if_expr.cond()));
    c_safety_checks_rec(
      f, new_guards, if_expr.false_case(), access_type, ns, dest); // rec. call
    return;
  }
  else if(expr.id() == ID_forall || expr.id() == ID_exists)
  {
    return;
  }

  // now do operands
  for(auto &op : expr.operands())
    c_safety_checks_rec(f, guards, op, access_type, ns, dest); // rec. call

  if(expr.id() == ID_dereference)
  {
    if(expr.type().id() == ID_code)
    {
      // dealt with elsewhere
    }
    else
    {
      auto size_opt = pointer_offset_size(expr.type(), ns);
      if(size_opt.has_value())
      {
        auto size = from_integer(*size_opt, size_type());
        auto pointer = to_dereference_expr(expr).pointer();
        auto condition = r_or_w_ok_exprt(
          access_type == access_typet::W ? ID_w_ok : ID_r_ok, pointer, size);
        condition.add_source_location() = expr.source_location();
        auto assertion_source_location = expr.source_location();
        assertion_source_location.set_property_class("pointer");
        auto pointer_text = expr2c(pointer, ns);
        assertion_source_location.set_comment(
          "pointer " + pointer_text + " safe");
        dest.add(goto_programt::make_assertion(
          guard(guards, condition), assertion_source_location));
      }
    }
  }
  else if(expr.id() == ID_div)
  {
    const auto &div_expr = to_div_expr(expr);
    if(
      div_expr.divisor().is_constant() &&
      !to_constant_expr(div_expr.divisor()).is_zero())
    {
    }
    else
    {
      auto zero = from_integer(0, div_expr.type());
      auto condition = implies_exprt(
        conjunction(guards), notequal_exprt(div_expr.divisor(), zero));
      auto source_location = expr.source_location();
      condition.add_source_location() = expr.source_location();
      source_location.set_property_class("division-by-zero");
      source_location.set_comment("division by zero in " + expr2c(expr, ns));
      dest.add(goto_programt::make_assertion(
        guard(guards, condition), source_location));
    }
  }
  else if(expr.id() == ID_mod)
  {
    const auto &mod_expr = to_mod_expr(expr);
    if(
      mod_expr.divisor().is_constant() &&
      !to_constant_expr(mod_expr.divisor()).is_zero())
    {
    }
    else
    {
      auto zero = from_integer(0, mod_expr.type());
      auto condition = notequal_exprt(mod_expr.divisor(), zero);
      auto source_location = expr.source_location();
      condition.add_source_location() = expr.source_location();
      source_location.set_property_class("division-by-zero");
      source_location.set_comment("division by zero in " + expr2c(expr, ns));
      dest.add(goto_programt::make_assertion(
        guard(guards, condition), source_location));
    }
  }
  else if(expr.id() == ID_index)
  {
    const auto &index_expr = to_index_expr(expr);
    auto zero = from_integer(0, index_expr.index().type());
    auto size = typecast_exprt::conditional_cast(
      index_array_size(index_expr.array().type()), index_expr.index().type());
    auto condition = and_exprt(
      binary_relation_exprt(zero, ID_le, index_expr.index()),
      binary_relation_exprt(size, ID_gt, index_expr.index()));
    // 'index' may not have a source location, e.g., when implicitly
    // taking the address of an array.
    auto source_location = expr.find_source_location();
    condition.add_source_location() = expr.source_location();
    source_location.set_property_class("array bounds");
    source_location.set_comment("array bounds in " + expr2c(expr, ns));
    dest.add(
      goto_programt::make_assertion(guard(guards, condition), source_location));
  }
}

void c_safety_checks(
  goto_functionst::function_mapt::value_type &f,
  const exprt &expr,
  access_typet access_type,
  const namespacet &ns,
  goto_programt &dest)
{
  c_safety_checks_rec(f, {}, expr, access_type, ns, dest);
}

static exprt offset_is_zero(const exprt &pointer)
{
  auto offset = pointer_offset(pointer);
  auto zero = from_integer(0, offset.type());
  return equal_exprt(std::move(offset), std::move(zero));
}

void c_safety_checks(
  goto_functionst::function_mapt::value_type &f,
  const namespacet &ns)
{
  auto &body = f.second.body;
  goto_programt dest;

  for(auto it = body.instructions.begin(); it != body.instructions.end(); it++)
  {
    if(it->is_assign())
    {
      c_safety_checks(f, it->assign_lhs(), access_typet::W, ns, dest);
      c_safety_checks(f, it->assign_rhs(), access_typet::R, ns, dest);
    }
    else if(it->is_function_call())
    {
      c_safety_checks(f, it->call_lhs(), access_typet::W, ns, dest);
      c_safety_checks(f, it->call_function(), access_typet::R, ns, dest);
      for(const auto &argument : it->call_arguments())
        c_safety_checks(f, argument, access_typet::R, ns, dest);
    }
    else
    {
      it->apply([&f, &ns, &dest](const exprt &expr) {
        c_safety_checks(f, expr, access_typet::R, ns, dest);
      });
    }

    if(it->is_function_call())
    {
      const auto &function = it->call_function();
      if(function.id() == ID_symbol)
      {
        const auto &identifier = to_symbol_expr(function).get_identifier();
        if(identifier == "free")
        {
          if(
            it->call_arguments().size() == 1 &&
            it->call_arguments()[0].type().id() == ID_pointer)
          {
            // Must be 1) dynamically allocated, 2) still alive,
            // 3) have offset zero, or, alternatively, NULL.
            const auto &pointer = it->call_arguments()[0];
            auto condition = or_exprt(
              equal_exprt(
                pointer, null_pointer_exprt(to_pointer_type(pointer.type()))),
              and_exprt(
                live_object_exprt(pointer),
                is_dynamic_object_exprt(pointer),
                offset_is_zero(pointer)));
            auto source_location = it->source_location();
            source_location.set_property_class("free");
            source_location.set_comment(
              "free argument must be valid dynamic object");
            dest.add(goto_programt::make_assertion(condition, source_location));
          }
        }
        else if(identifier == "realloc")
        {
          if(
            it->call_arguments().size() == 2 &&
            it->call_arguments()[0].type().id() == ID_pointer)
          {
            // Must be 1) dynamically allocated, 2) still alive,
            // 3) have offset zero, or, alternatively, NULL.
            const auto &pointer = it->call_arguments()[0];
            auto condition = or_exprt(
              equal_exprt(
                pointer, null_pointer_exprt(to_pointer_type(pointer.type()))),
              and_exprt(
                live_object_exprt(pointer),
                is_dynamic_object_exprt(pointer),
                offset_is_zero(pointer)));
            auto source_location = it->source_location();
            source_location.set_property_class("realloc");
            source_location.set_comment(
              "realloc argument must be valid dynamic object");
            dest.add(goto_programt::make_assertion(condition, source_location));
          }
        }
        else if(identifier == "memcmp")
        {
          if(
            it->call_arguments().size() == 3 &&
            it->call_arguments()[0].type().id() == ID_pointer &&
            it->call_arguments()[1].type().id() == ID_pointer &&
            it->call_arguments()[2].type().id() == ID_unsignedbv)
          {
            // int memcmp(const void *s1, const void *s2, size_t n);
            const auto &p1 = it->call_arguments()[0];
            const auto &p2 = it->call_arguments()[1];
            const auto &size = it->call_arguments()[2];
            auto condition =
              and_exprt(r_ok_exprt(p1, size), r_ok_exprt(p2, size));
            auto source_location = it->source_location();
            source_location.set_property_class("memcmp");
            source_location.set_comment("memcmp regions must be valid");
            dest.add(goto_programt::make_assertion(condition, source_location));
          }
        }
        else if(identifier == "memchr")
        {
          if(
            it->call_arguments().size() == 3 &&
            it->call_arguments()[0].type().id() == ID_pointer &&
            it->call_arguments()[2].type().id() == ID_unsignedbv)
          {
            // void *memchr(const void *, int, size_t);
            const auto &p = it->call_arguments()[0];
            const auto &size = it->call_arguments()[2];
            auto condition = r_ok_exprt(p, size);
            auto source_location = it->source_location();
            source_location.set_property_class("memchr");
            source_location.set_comment("memchr source must be valid");
            dest.add(goto_programt::make_assertion(condition, source_location));
          }
        }
        else if(identifier == "memset")
        {
          if(
            it->call_arguments().size() == 3 &&
            it->call_arguments()[0].type().id() == ID_pointer &&
            it->call_arguments()[2].type().id() == ID_unsignedbv)
          {
            // void *memset(void *b, int c, size_t len);
            const auto &pointer = it->call_arguments()[0];
            const auto &size = it->call_arguments()[2];
            auto condition = w_ok_exprt(pointer, size);
            auto source_location = it->source_location();
            source_location.set_property_class("memset");
            source_location.set_comment("memset destination must be valid");
            dest.add(goto_programt::make_assertion(condition, source_location));
          }
        }
        else if(identifier == "strlen")
        {
          if(
            it->call_arguments().size() == 1 &&
            it->call_arguments()[0].type().id() == ID_pointer)
          {
            const auto &address = it->call_arguments()[0];
            auto condition = is_cstring_exprt(address);
            auto source_location = it->source_location();
            source_location.set_property_class("strlen");
            source_location.set_comment("strlen argument must be C string");
            dest.add(goto_programt::make_assertion(condition, source_location));
          }
        }
        else if(identifier == "__builtin___memset_chk") // clang variant
        {
          if(
            it->call_arguments().size() == 4 &&
            it->call_arguments()[0].type().id() == ID_pointer &&
            it->call_arguments()[2].type().id() == ID_unsignedbv)
          {
            const auto &pointer = it->call_arguments()[0];
            const auto &size = it->call_arguments()[2];
            auto condition = w_ok_exprt(pointer, size);
            auto source_location = it->source_location();
            source_location.set_property_class("memset");
            source_location.set_comment("memset destination must be valid");
            dest.add(goto_programt::make_assertion(condition, source_location));
          }
        }
      }
    }

    std::size_t n = dest.instructions.size();
    if(n != 0)
    {
      body.insert_before_swap(it, dest);
      dest.clear();
      it = std::next(it, n);
    }
  }
}

void c_safety_checks(goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  for(auto &f : goto_model.goto_functions.function_map)
    c_safety_checks(f, ns);

  // update the numbering
  goto_model.goto_functions.compute_location_numbers();
}

void no_assertions(goto_functionst::function_mapt::value_type &f)
{
  auto &body = f.second.body;

  for(auto it = body.instructions.begin(); it != body.instructions.end(); it++)
  {
    if(
      it->is_assert() &&
      it->source_location().get_property_class() == ID_assertion)
    {
      it->turn_into_skip();
    }
  }
}

void no_assertions(goto_modelt &goto_model)
{
  for(auto &f : goto_model.goto_functions.function_map)
    no_assertions(f);
}
