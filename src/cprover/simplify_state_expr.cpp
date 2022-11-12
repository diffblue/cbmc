/*******************************************************************\

Module: Simplify State Expressions

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Simplify State Expressions

#include "simplify_state_expr.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/expr_util.h>
#include <util/format_expr.h>
#include <util/format_type.h>
#include <util/mathematical_expr.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include "may_alias.h"
#include "may_be_same_object.h"
#include "sentinel_dll.h"
#include "state.h"

#include <iostream>

std::size_t allocate_counter = 0;

exprt simplify_state_expr_node(
  exprt,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &);

static bool types_are_compatible(const typet &a, const typet &b)
{
  if(a == b)
    return true;
  else if(a.id() == ID_pointer && b.id() == ID_pointer)
    return true;
  else
    return false;
}

static bool is_char(const typet &type)
{
  if(type.id() == ID_signedbv || type.id() == ID_unsignedbv)
    return to_bitvector_type(type).get_width() == config.ansi_c.char_width;
  else
    return false;
}

exprt simplify_evaluate_update(
  evaluate_exprt evaluate_expr,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns)
{
  PRECONDITION(evaluate_expr.state().id() == ID_update_state);

  const auto &update_state_expr = to_update_state_expr(evaluate_expr.state());

#if 0
  std::cout << "U: " << format(update_state_expr) << "\n";
  std::cout << "u: " << format(update_state_expr.address()) << "\n";
  std::cout << "T: " << format(update_state_expr.address().type()) << "\n";
  std::cout << "E: " << format(evaluate_expr.address()) << "\n";
  std::cout << "T: " << format(evaluate_expr.address().type()) << "\n";
#endif

  auto may_alias = ::may_alias(
    evaluate_expr.address(), update_state_expr.address(), address_taken, ns);

#if 0
  if(may_alias.has_value())
    std::cout << "M: " << format(*may_alias) << "\n";
  else
    std::cout << "M: ?\n";
#endif

  if(may_alias.has_value())
  {
    // 'simple' case
    if(may_alias->is_true())
    {
      // The object is known to be the same.
      // (ς[A:=V])(A) --> V
      return simplify_state_expr_node(
        typecast_exprt::conditional_cast(
          update_state_expr.new_value(), evaluate_expr.type()),
        address_taken,
        ns);
    }
    else if(may_alias->is_false())
    {
      // The object is known to be different.
      // (ς[❝x❞:=V])(❝y❞) --> ς(❝y❞)
      // It might be possible to further simplify ς(❝y❞).
      return simplify_state_expr_node(
        evaluate_expr.with_state(update_state_expr.state()), address_taken, ns);
    }
    else
    {
      // The object may or may not be the same.
      // (ς[A:=V])(B) --> if cond then V else ς(B) endif
      auto simplified_cond = simplify_state_expr(*may_alias, address_taken, ns);
      auto new_evaluate_expr =
        evaluate_expr.with_state(update_state_expr.state());
      auto simplified_new_evaluate_expr = simplify_state_expr_node(
        new_evaluate_expr, address_taken, ns); // rec. call
      auto if_expr = if_exprt(
        std::move(simplified_cond),
        simplify_state_expr_node(
          typecast_exprt::conditional_cast(
            update_state_expr.new_value(), evaluate_expr.type()),
          address_taken,
          ns),
        std::move(simplified_new_evaluate_expr));
      return simplify_expr(if_expr, ns);
    }
  }

  auto new_evaluate_expr = evaluate_expr.with_state(update_state_expr.state());
  auto simplified_new_evaluate_expr =
    simplify_state_expr(new_evaluate_expr, address_taken, ns); // rec. call

  // Types are compatible?
  if(types_are_compatible(
       update_state_expr.new_value().type(), evaluate_expr.type()))
  {
    // Disregard case where the two memory regions overlap.
    //
    // (ς[w:=v])(r) -->
    //   IF same_object(w, r) ∧ offset(w) = offset(r) THEN
    //     v
    //   ELSE
    //     ς(r)
    //   ENDIF
    auto same_object =
      ::same_object(evaluate_expr.address(), update_state_expr.address());

    auto simplified_same_object =
      simplify_state_expr(same_object, address_taken, ns);

    auto offset_w = simplify_state_expr(
      pointer_offset(evaluate_expr.address()), address_taken, ns);

    auto offset_r = simplify_state_expr(
      pointer_offset(update_state_expr.address()), address_taken, ns);

    auto same_offset = equal_exprt(offset_w, offset_r);

    auto same = and_exprt(simplified_same_object, same_offset);

    auto simplified_same =
      simplify_state_expr(simplify_expr(same, ns), address_taken, ns);

    auto new_value = typecast_exprt::conditional_cast(
      update_state_expr.new_value(), evaluate_expr.type());

    auto if_expr =
      if_exprt(simplified_same, new_value, simplified_new_evaluate_expr);

    return simplify_expr(if_expr, ns);
  }
  else if(is_char(simplified_new_evaluate_expr.type()))
  {
    // We are reading a byte. Use byte_extract.
    //
    // (ς[w:=v])(r) -->
    //   IF same_object(w, r) THEN
    //     byte_extract(v, r-w)
    //   ELSE
    //     ς(r)
    //   ENDIF
    auto new_value = update_state_expr.new_value();

    auto offset_r = simplify_state_expr(
      pointer_offset(evaluate_expr.address()), address_taken, ns);

    auto offset_w = simplify_state_expr(
      pointer_offset(update_state_expr.address()), address_taken, ns);

    auto offset = minus_exprt(offset_r, offset_w);

    auto same_object =
      ::same_object(evaluate_expr.address(), update_state_expr.address());

    auto simplified_same_object =
      simplify_state_expr(same_object, address_taken, ns);

    auto byte_extract =
      make_byte_extract(new_value, offset, evaluate_expr.type());

    return if_exprt(
      std::move(simplified_same_object),
      std::move(byte_extract),
      std::move(simplified_new_evaluate_expr));
  }
  else
  {
    // Complex case. Types don't match.
    return simplified_new_evaluate_expr;

#if 0
    auto object = update_state_expr.new_value();

    auto offset = simplify_state_expr_node(
      pointer_offset(evaluate_expr.address()), address_taken, ns);

    auto byte_extract = make_byte_extract(object, offset, evaluate_expr.type());

    return if_exprt(
      std::move(simplified_same_object),
      std::move(byte_extract),
      std::move(simplified_new_evaluate_expr));
#endif
  }
}

exprt simplify_allocate(allocate_exprt src)
{
  // A store does not affect the result.
  // allocate(ς[A:=V]), size) --> allocate(ς, size)
  if(src.state().id() == ID_update_state)
  {
    // rec. call
    return simplify_allocate(
      src.with_state(to_update_state_expr(src.state()).state()));
  }
  else if(src.state().id() == ID_enter_scope_state)
  {
    // rec. call
    return simplify_allocate(
      src.with_state(to_enter_scope_state_expr(src.state()).state()));
  }
  else if(src.state().id() == ID_exit_scope_state)
  {
    // rec. call
    return simplify_allocate(
      src.with_state(to_exit_scope_state_expr(src.state()).state()));
  }

  return std::move(src);
}

exprt simplify_evaluate_allocate_state(
  evaluate_exprt evaluate_expr,
  const namespacet &ns)
{
  PRECONDITION(evaluate_expr.state().id() == ID_allocate_state);

  //  const auto &allocate_expr = to_allocate_expr(evaluate_expr.state());

#if 0
  // Same address?
  if(evaluate_expr.address() == allocate_expr.address())
  {
#  if 0
    irep_idt identifier = "allocate-" + std::to_string(++allocate_counter);
    auto object_size = allocate_expr.size();
    auto object_type = array_typet(char_type(), object_size);
    auto symbol_expr = symbol_exprt(identifier, object_type);
    return object_address_exprt(symbol_expr);
#  endif
    return std::move(evaluate_expr);
  }
  else // different
  {
    auto new_evaluate_expr = evaluate_expr;
    new_evaluate_expr.state() = allocate_expr.state();
    return std::move(new_evaluate_expr);
  }
#endif
  return std::move(evaluate_expr);
}

exprt simplify_evaluate_deallocate_state(
  evaluate_exprt evaluate_expr,
  const namespacet &ns)
{
  PRECONDITION(evaluate_expr.state().id() == ID_deallocate_state);

  // deallocate isn't visible to 'evaluate'
  const auto &deallocate_state_expr =
    to_deallocate_state_expr(evaluate_expr.state());
  auto new_evaluate_expr =
    evaluate_expr.with_state(deallocate_state_expr.state());
  return std::move(new_evaluate_expr);
}

exprt simplify_evaluate_enter_scope_state(
  evaluate_exprt evaluate_expr,
  const namespacet &ns)
{
  PRECONDITION(evaluate_expr.state().id() == ID_enter_scope_state);

  const auto &enter_scope_state_expr =
    to_enter_scope_state_expr(evaluate_expr.state());
  auto new_evaluate_expr =
    evaluate_expr.with_state(enter_scope_state_expr.state());
  return std::move(new_evaluate_expr);
}

exprt simplify_evaluate_exit_scope_state(
  evaluate_exprt evaluate_expr,
  const namespacet &ns)
{
  PRECONDITION(evaluate_expr.state().id() == ID_exit_scope_state);

  const auto &exit_scope_state_expr =
    to_exit_scope_state_expr(evaluate_expr.state());
  auto new_evaluate_expr =
    evaluate_expr.with_state(exit_scope_state_expr.state());
  return std::move(new_evaluate_expr);
}

exprt simplify_object_expression_rec(exprt src)
{
  if(src.id() == ID_object_address)
    return src;
  else if(src.id() == ID_element_address)
    return simplify_object_expression_rec(to_element_address_expr(src).base());
  else if(src.id() == ID_field_address)
    return simplify_object_expression_rec(to_field_address_expr(src).base());
  else if(src.id() == ID_plus)
  {
    const auto &plus_expr = to_plus_expr(src);
    for(auto &op : plus_expr.operands())
      if(op.type().id() == ID_pointer)
        return simplify_object_expression_rec(op);
    return src; // no change
  }
  else if(src.id() == ID_typecast)
  {
    const auto &op = to_typecast_expr(src).op();
    if(op.type().id() == ID_pointer)
      return simplify_object_expression_rec(op);
    else
      return src; // no change
  }
  else
    return src;
}

exprt simplify_object_expression(exprt src)
{
  return simplify_object_expression_rec(src);
}

exprt simplify_live_object_expr(
  state_live_object_exprt src,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns)
{
  const auto &pointer = src.address();

  auto object = simplify_object_expression(pointer);

  if(object.id() == ID_object_address)
  {
    auto identifier = to_object_address_expr(object).object_identifier();

    if(has_prefix(id2string(identifier), "allocate-"))
    {
    }
    else if(identifier == "return_value")
    {
      return true_exprt(); // never dies
    }
    else if(has_prefix(id2string(identifier), "va_args::"))
    {
      return true_exprt(); // might be 'dead'
    }
    else
    {
      const auto &symbol = ns.lookup(identifier);
      if(symbol.is_static_lifetime)
      {
        return true_exprt(); // always live
      }
    }
  }

  // A store does not affect the result.
  // live_object(ς[A:=V]), p) --> live_object(ς, p)
  if(src.state().id() == ID_update_state)
  {
    src.state() = to_update_state_expr(src.state()).state();

    // rec. call
    return simplify_live_object_expr(std::move(src), address_taken, ns);
  }
  else if(src.state().id() == ID_deallocate_state)
  {
    const auto &deallocate_state_expr = to_deallocate_state_expr(src.state());
    // live_object(deallocate_state(ς, p), q) -->
    //   IF same_object(p, q) THEN false ELSE live_object(ς, q) ENDIF
    auto same_object = ::same_object(object, deallocate_state_expr.address());
    auto simplified_same_object =
      simplify_state_expr(same_object, address_taken, ns);
    auto new_live_object_expr = simplify_live_object_expr(
      src.with_state(deallocate_state_expr.state()), address_taken, ns);
    return if_exprt(
      simplified_same_object, false_exprt(), new_live_object_expr);
  }
  else if(src.state().id() == ID_enter_scope_state)
  {
    // This begins the life of a local-scoped variable.
    const auto &enter_scope_state_expr = to_enter_scope_state_expr(src.state());
    if(
      address_taken.find(enter_scope_state_expr.symbol()) !=
      address_taken.end())
    {
      // live_object(enter_scope_state(ς, p), q) -->
      //   IF same_object(p, q) THEN true ELSE live_object(ς, q) ENDIF
      auto same_object =
        ::same_object(object, enter_scope_state_expr.address());
      auto simplified_same_object =
        simplify_state_expr(same_object, address_taken, ns);
      auto new_live_object_expr = simplify_live_object_expr( // rec. call
        src.with_state(enter_scope_state_expr.state()),
        address_taken,
        ns);
      return if_exprt(
        simplified_same_object, true_exprt(), new_live_object_expr);
    }
    else
    {
      return simplify_live_object_expr( // rec. call
        src.with_state(enter_scope_state_expr.state()),
        address_taken,
        ns);
    }
  }
  else if(src.state().id() == ID_exit_scope_state)
  {
    // This ends the life of a local-scoped variable.
    const auto &exit_scope_state_expr = to_exit_scope_state_expr(src.state());
    if(
      address_taken.find(exit_scope_state_expr.symbol()) != address_taken.end())
    {
      // live_object(exit_scope_state(ς, p), q) -->
      //   IF same_object(p, q) THEN false ELSE live_object(ς, q) ENDIF
      auto same_object = ::same_object(object, exit_scope_state_expr.address());
      auto simplified_same_object =
        simplify_state_expr(same_object, address_taken, ns);
      auto new_live_object_expr = simplify_live_object_expr( // rec. call
        src.with_state(exit_scope_state_expr.state()),
        address_taken,
        ns);
      return if_exprt(
        simplified_same_object, false_exprt(), new_live_object_expr);
    }
    else
    {
      return simplify_live_object_expr( // rec. call
        src.with_state(exit_scope_state_expr.state()),
        address_taken,
        ns);
    }
  }

  return std::move(src);
}

exprt simplify_writeable_object_expr(
  state_writeable_object_exprt src,
  const namespacet &ns)
{
  const auto &pointer = src.address();

  auto object = simplify_object_expression(pointer);

  if(object.id() == ID_object_address)
  {
    auto identifier = to_object_address_expr(object).object_identifier();

    if(has_prefix(id2string(identifier), "allocate-"))
    {
    }
    else if(has_prefix(id2string(identifier), "va_args::"))
    {
      return true_exprt(); // always writeable
    }
    else
    {
      const auto &symbol = ns.lookup(identifier);
      return make_boolean_expr(!symbol.type.get_bool(ID_C_constant));
    }
  }

  // A store does not affect the result.
  // writeable_object(ς[A:=V]), p) --> writeable_object(ς, p)
  if(src.state().id() == ID_update_state)
  {
    src.state() = to_update_state_expr(src.state()).state();
    return std::move(src);
  }

  return std::move(src);
}

exprt simplify_is_dynamic_object_expr(state_is_dynamic_object_exprt src)
{
  const auto &pointer = src.address();

  auto object = simplify_object_expression(pointer);

  if(object.id() == ID_object_address)
  {
    // these are not dynamic
    return false_exprt();
  }

  // A store does not affect the result.
  // is_dynamic_object(ς[A:=V]), p) --> is_dynamic_object(ς, p)
  if(src.state().id() == ID_update_state)
  {
    src.state() = to_update_state_expr(src.state()).state();
    // rec. call
    return simplify_is_dynamic_object_expr(std::move(src));
  }
  else if(src.state().id() == ID_enter_scope_state)
  {
    return simplify_is_dynamic_object_expr(
      src.with_state(to_enter_scope_state_expr(src.state()).state()));
  }
  else if(src.state().id() == ID_exit_scope_state)
  {
    return simplify_is_dynamic_object_expr(
      src.with_state(to_exit_scope_state_expr(src.state()).state()));
  }

  return std::move(src);
}

exprt simplify_object_size_expr(
  state_object_size_exprt src,
  const namespacet &ns)
{
  const auto &pointer = src.address();

  auto object = simplify_object_expression(pointer);

  if(object.id() == ID_object_address)
  {
    const auto &object_address_expr = to_object_address_expr(object);
    auto size_opt = size_of_expr(object_address_expr.object_type(), ns);
    if(size_opt.has_value())
      return typecast_exprt::conditional_cast(*size_opt, src.type());
    else
      return std::move(src); // no change
  }

  // A store does not affect the result.
  // object_size(ς[A:=V]), p) --> object_size(ς, p)
  if(src.state().id() == ID_update_state)
  {
    return src.with_state(to_update_state_expr(src.state()).state());
  }

  return std::move(src);
}

exprt simplify_ok_expr(
  state_ok_exprt src,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns)
{
  auto &state = src.state();
  auto &pointer = src.address();
  auto &size = src.size();

  if(state.id() == ID_update_state)
  {
    // A store does not affect the result.
    // X_ok(ς[A:=V]), A, S) --> X_ok(ς, A, S)
    state = to_update_state_expr(state).state();

    // rec. call
    return simplify_state_expr_node(std::move(src), address_taken, ns);
  }
  else if(state.id() == ID_enter_scope_state)
  {
    const auto &enter_scope_state_expr = to_enter_scope_state_expr(state);

    // rec. call
    auto rec_result = simplify_state_expr_node(
      src.with_state(enter_scope_state_expr.state()), address_taken, ns);

#if 0
    // replace array by array[0]
    auto enter_scope_address =
      enter_scope_state_expr.object_type().id() == ID_array ?
        element_address_exprt(enter_scope_state_expr.address(), from_integer(0, to_array_type(enter_scope_state_expr.object_type()).index_type())) :
        enter_scope_state_expr.address();

    auto may_alias =
      ::may_alias(enter_scope_address, pointer, address_taken, ns);

    if(may_alias.has_value() && *may_alias == false_exprt())
      return rec_result;

    auto same_object = ::same_object(pointer, enter_scope_state_expr.address());
#else
    auto same_object = may_be_same_object(
      pointer, enter_scope_state_expr.address(), address_taken, ns);
#endif

    auto simplified_same_object =
      simplify_state_expr(same_object, address_taken, ns);

    // Known to be live, only need to check upper bound.
    // Extend one bit, to cover overflow case.
    auto size_type = ::size_type();
    auto size_type_ext = unsignedbv_typet(size_type.get_width() + 1);
    auto offset = pointer_offset_exprt(pointer, size_type_ext);
    auto size_casted = typecast_exprt(size, size_type_ext);
    auto object_size_opt =
      size_of_expr(enter_scope_state_expr.object_type(), ns);
    if(!object_size_opt.has_value())
      return std::move(src);

    auto upper = binary_relation_exprt(
      plus_exprt(offset, size_casted),
      ID_le,
      typecast_exprt(*object_size_opt, size_type_ext));

    auto simplified_upper = simplify_state_expr(upper, address_taken, ns);

    auto implication =
      if_exprt(simplified_same_object, simplified_upper, rec_result);

    return std::move(implication);
  }
  else if(state.id() == ID_exit_scope_state)
  {
#if 0
    const auto &exit_scope_state_expr = to_exit_scope_state_expr(state);

    // rec. call
    auto rec_result = simplify_state_expr_node(
      src.with_state(exit_scope_state_expr.state()), address_taken, ns);

    auto same_object = ::same_object(pointer, exit_scope_state_expr.address());

    auto simplified_same_object =
      simplify_state_expr(same_object, address_taken, ns);

    // Known to be dead if it's the same object.
    auto implication =
      if_exprt(simplified_same_object, false_exprt(), rec_result);

    return implication;
#else
    return simplify_state_expr_node(
      src.with_state(to_exit_scope_state_expr(state).state()),
      address_taken,
      ns);
#endif
  }

  return std::move(src);
}

#if 0
static bool is_one(const exprt &src)
{
  if(src.id() == ID_typecast)
    return is_one(to_typecast_expr(src).op());
  else if(src.id() == ID_constant)
  {
    auto value_opt = numeric_cast<mp_integer>(src);
    return value_opt.has_value() && *value_opt == 1;
  }
  else
    return false;
}
#endif

static bool is_a_char_type(const typet &type)
{
  return (type.id() == ID_signedbv || type.id() == ID_unsignedbv) &&
         to_bitvector_type(type).get_width() == char_type().get_width();
}

static bool is_zero_char(const exprt &src, const namespacet &ns)
{
  if(!is_a_char_type(src.type()))
    return false;

  auto src_simplified = simplify_expr(src, ns);

  auto integer_opt = numeric_cast<mp_integer>(src);

  return integer_opt.has_value() && *integer_opt == 0;
}

exprt simplify_is_cstring_expr(
  state_is_cstring_exprt src,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns)
{
  PRECONDITION(src.type().id() == ID_bool);
  const auto &state = src.state();
  const auto &pointer = src.address();

  if(state.id() == ID_update_state)
  {
    const auto &update_state_expr = to_update_state_expr(state);

    auto cstring_in_old_state = src;
    cstring_in_old_state.op0() = update_state_expr.state();
    auto simplified_cstring_in_old_state =
      simplify_state_expr_node(cstring_in_old_state, address_taken, ns);

    auto may_alias =
      ::may_alias(pointer, update_state_expr.address(), address_taken, ns);

    if(may_alias.has_value() && may_alias->is_false())
    {
      // different objects
      // cstring(s[x:=v], p) --> cstring(s, p)
      return simplified_cstring_in_old_state;
    }

    // maybe the same

    // Are we writing zero?
    if(update_state_expr.new_value().is_zero())
    {
      // cstring(s[p:=0], q) --> if p alias q then true else cstring(s, q)
      auto same_object = ::same_object(pointer, update_state_expr.address());

      auto simplified_same_object =
        simplify_expr(simplify_state_expr(same_object, address_taken, ns), ns);

      return if_exprt(
        simplified_same_object, true_exprt(), simplified_cstring_in_old_state);
    }
  }
  else if(state.id() == ID_enter_scope_state)
  {
    // rec. call
    return simplify_is_cstring_expr(
      src.with_state(to_enter_scope_state_expr(state).state()),
      address_taken,
      ns);
  }
  else if(state.id() == ID_exit_scope_state)
  {
    // rec. call
    return simplify_is_cstring_expr(
      src.with_state(to_exit_scope_state_expr(state).state()),
      address_taken,
      ns);
  }

  if(pointer.id() == ID_plus)
  {
#if 0
    auto &plus_expr = to_plus_expr(pointer);
    if(plus_expr.operands().size() == 2 && is_one(plus_expr.op1()))
    {
      // is_cstring(ς, p + 1)) --> is_cstring(ς, p) ∨ ς(p)=0
      auto new_is_cstring = src;
      new_is_cstring.op1() = plus_expr.op0();
      auto type = to_pointer_type(pointer.type()).base_type();
      auto zero = from_integer(0, type);
      auto is_zero =
        equal_exprt(evaluate_exprt(state, plus_expr.op0(), type), zero);
      return or_exprt(new_is_cstring, is_zero);
    }
#endif
  }
  else if(
    pointer.id() == ID_address_of &&
    to_address_of_expr(pointer).object().id() == ID_string_constant)
  {
    // is_cstring(ς, &"...")) --> true
    return true_exprt();
  }
  else if(
    pointer.id() == ID_element_address &&
    to_element_address_expr(pointer).base().id() == ID_address_of &&
    to_address_of_expr(to_element_address_expr(pointer).base()).object().id() ==
      ID_string_constant)
  {
    // TODO: compare offset to length
    // is_cstring(ς, element_address(&"...", 0))) --> true
    return true_exprt();
  }

  return std::move(src);
}

exprt simplify_cstrlen_expr(
  state_cstrlen_exprt src,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns)
{
  const auto &state = src.state();
  const auto &pointer = src.address();

  if(state.id() == ID_update_state)
  {
    const auto &update_state_expr = to_update_state_expr(state);

    auto cstrlen_in_old_state = src.with_state(update_state_expr.state());
    auto simplified_cstrlen_in_old_state =
      simplify_state_expr_node(cstrlen_in_old_state, address_taken, ns);

    auto may_be_same_object = ::may_be_same_object(
      pointer, update_state_expr.address(), address_taken, ns);

    if(may_be_same_object.is_false())
    {
      // different objects
      // cstrlen(s[x:=v], p) --> cstrlen(s, p)
      return simplified_cstrlen_in_old_state;
    }

    // maybe the same

    // Are we writing zero?
    if(is_zero_char(update_state_expr.new_value(), ns))
    {
      // cstrlen(s[p:=0], p) --> 0
      if(pointer == update_state_expr.address())
        return from_integer(0, src.type());
    }
  }

  if(pointer.id() == ID_plus)
  {
#if 0
    auto &plus_expr = to_plus_expr(pointer);
    if(plus_expr.operands().size() == 2 && is_one(plus_expr.op1()))
    {
      // is_cstring(ς, p + 1)) --> is_cstring(ς, p) ∨ ς(p)=0
      auto new_is_cstring = src;
      new_is_cstring.op1() = plus_expr.op0();
      auto type = to_pointer_type(pointer.type()).base_type();
      auto zero = from_integer(0, type);
      auto is_zero =
        equal_exprt(evaluate_exprt(state, plus_expr.op0(), type), zero);
      return or_exprt(new_is_cstring, is_zero);
    }
#endif
  }
  else if(
    pointer.id() == ID_address_of &&
    to_address_of_expr(pointer).object().id() == ID_string_constant)
  {
#if 0
    // is_cstring(ς, &"...")) --> true
    return true_exprt();
#endif
  }
  else if(
    pointer.id() == ID_element_address &&
    to_element_address_expr(pointer).base().id() == ID_address_of &&
    to_address_of_expr(to_element_address_expr(pointer).base()).object().id() ==
      ID_string_constant)
  {
#if 0
    // TODO: compare offset to length
    // is_cstring(ς, element_address(&"...", 0))) --> true
    return true_exprt();
#endif
  }

  return std::move(src);
}

exprt simplify_is_sentinel_dll_expr(
  state_is_sentinel_dll_exprt src,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns)
{
  PRECONDITION(src.type().id() == ID_bool);
  const auto &state = src.state();
  const auto &head = src.head();
  const auto &tail = src.tail();

  {
    // ς(h.❝n❞) = t ∧ ς(t.❝p❞) = h --> is_sentinel_dll(ς, h, t)
    auto head_next = sentinel_dll_next(state, head, ns);
    auto tail_prev = sentinel_dll_prev(state, tail, ns);

    if(head_next.has_value() && tail_prev.has_value())
    {
      // rec. calls
      auto head_next_simplified =
        simplify_state_expr(*head_next, address_taken, ns);
      auto tail_prev_simplified =
        simplify_state_expr(*tail_prev, address_taken, ns);
      if(head_next_simplified == tail && tail_prev_simplified == head)
        return true_exprt();
    }
  }

  if(state.id() == ID_update_state)
  {
    const auto &update_state_expr = to_update_state_expr(state);

    // are we writing to something that might be a node pointer?
    const auto &update_type = update_state_expr.new_value().type();
    if(update_type != src.head().type())
    {
      // update is irrelevant, drop update
      auto without_update = src.with_state(update_state_expr.state());
      return simplify_is_sentinel_dll_expr(without_update, address_taken, ns);
    }
  }
  else if(state.id() == ID_enter_scope_state)
  {
    return simplify_is_sentinel_dll_expr(
      src.with_state(to_enter_scope_state_expr(state).state()),
      address_taken,
      ns);
  }
  else if(state.id() == ID_exit_scope_state)
  {
    return simplify_is_sentinel_dll_expr(
      src.with_state(to_exit_scope_state_expr(state).state()),
      address_taken,
      ns);
  }

  return std::move(src);
}

exprt simplify_pointer_offset_expr(
  pointer_offset_exprt src,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns)
{
  if(src.pointer().id() == ID_object_address)
  {
    // pointer_offset(❝x❞) -> 0
    return from_integer(0, src.type());
  }
  else if(src.pointer().id() == ID_element_address)
  {
    const auto &element_address_expr = to_element_address_expr(src.pointer());
    // pointer_offset(element_address(Z, y)) -->
    //   pointer_offset(Z) + y*sizeof(x)
    auto size_opt = size_of_expr(element_address_expr.element_type(), ns);
    if(size_opt.has_value())
    {
      auto product = mult_exprt(
        typecast_exprt::conditional_cast(
          element_address_expr.index(), src.type()),
        typecast_exprt::conditional_cast(*size_opt, src.type()));
      auto pointer_offset = simplify_pointer_offset_expr(
        pointer_offset_exprt(element_address_expr.base(), src.type()),
        address_taken,
        ns);
      auto sum = plus_exprt(pointer_offset, std::move(product));
      return std::move(sum);
    }
  }
  else if(src.pointer().id() == ID_address_of)
  {
    const auto &address_of_expr = to_address_of_expr(src.pointer());
    if(address_of_expr.object().id() == ID_string_constant)
      return from_integer(0, src.type());
  }
  else if(src.pointer().id() == ID_typecast)
  {
    if(to_typecast_expr(src.pointer()).op().type().id() == ID_pointer)
    {
      // remove the typecast
      return simplify_pointer_offset_expr(
        pointer_offset_exprt(to_typecast_expr(src.pointer()).op(), src.type()),
        address_taken,
        ns);
    }
  }

  return std::move(src);
}

exprt simplify_pointer_object_expr(
  pointer_object_exprt src,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns)
{
  auto simplified_pointer = simplify_object_expression_rec(src.pointer());

  if(src.pointer() != simplified_pointer)
    return pointer_object_exprt(simplified_pointer, src.type());

  return std::move(src);
}

exprt simplify_state_expr_node(
  exprt src,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns)
{
  if(src.id() == ID_allocate)
  {
    return simplify_allocate(to_allocate_expr(src));
  }
  else if(src.id() == ID_evaluate)
  {
    auto &evaluate_expr = to_evaluate_expr(src);

    if(evaluate_expr.state().id() == ID_update_state)
    {
      return simplify_evaluate_update(evaluate_expr, address_taken, ns);
    }
    else if(evaluate_expr.state().id() == ID_allocate_state)
    {
      return simplify_evaluate_allocate_state(evaluate_expr, ns);
    }
    else if(evaluate_expr.state().id() == ID_deallocate_state)
    {
      return simplify_evaluate_deallocate_state(evaluate_expr, ns);
    }
    else if(evaluate_expr.state().id() == ID_enter_scope_state)
    {
      return simplify_evaluate_enter_scope_state(evaluate_expr, ns);
    }
    else if(evaluate_expr.state().id() == ID_exit_scope_state)
    {
      return simplify_evaluate_exit_scope_state(evaluate_expr, ns);
    }
  }
  else if(
    src.id() == ID_state_r_ok || src.id() == ID_state_w_ok ||
    src.id() == ID_state_rw_ok)
  {
    return simplify_ok_expr(to_state_ok_expr(src), address_taken, ns);
  }
  else if(src.id() == ID_state_live_object)
  {
    return simplify_live_object_expr(
      to_state_live_object_expr(src), address_taken, ns);
  }
  else if(src.id() == ID_state_writeable_object)
  {
    return simplify_writeable_object_expr(
      to_state_writeable_object_expr(src), ns);
  }
  else if(src.id() == ID_state_is_cstring)
  {
    return simplify_is_cstring_expr(
      to_state_is_cstring_expr(src), address_taken, ns);
  }
  else if(src.id() == ID_state_cstrlen)
  {
    return simplify_cstrlen_expr(to_state_cstrlen_expr(src), address_taken, ns);
  }
  else if(src.id() == ID_state_is_sentinel_dll)
  {
    return simplify_is_sentinel_dll_expr(
      to_state_is_sentinel_dll_expr(src), address_taken, ns);
  }
  else if(src.id() == ID_state_is_dynamic_object)
  {
    return simplify_is_dynamic_object_expr(
      to_state_is_dynamic_object_expr(src));
  }
  else if(src.id() == ID_plus)
  {
    auto &plus_expr = to_plus_expr(src);
    if(
      src.type().id() == ID_pointer &&
      plus_expr.op0().id() == ID_element_address)
    {
      // element_address(X, Y) + Z --> element_address(X, Y + Z)
      auto new_element_address_expr = to_element_address_expr(plus_expr.op0());
      new_element_address_expr.index() = plus_exprt(
        new_element_address_expr.index(),
        typecast_exprt::conditional_cast(
          plus_expr.op1(), new_element_address_expr.index().type()));
      new_element_address_expr.index() =
        simplify_expr(new_element_address_expr.index(), ns);
      return simplify_state_expr_node(
        new_element_address_expr, address_taken, ns);
    }
  }
  else if(src.id() == ID_pointer_offset)
  {
    return simplify_pointer_offset_expr(
      to_pointer_offset_expr(src), address_taken, ns);
  }
  else if(src.id() == ID_pointer_object)
  {
    return simplify_pointer_object_expr(
      to_pointer_object_expr(src), address_taken, ns);
  }
  else if(src.id() == ID_state_object_size)
  {
    return simplify_object_size_expr(to_state_object_size_expr(src), ns);
  }
  else if(src.id() == ID_equal)
  {
    const auto &equal_expr = to_equal_expr(src);
    if(
      equal_expr.lhs().id() == ID_pointer_object &&
      equal_expr.rhs().id() == ID_pointer_object)
    {
      const auto &lhs_p = to_pointer_object_expr(equal_expr.lhs()).pointer();
      const auto &rhs_p = to_pointer_object_expr(equal_expr.rhs()).pointer();
      if(lhs_p.id() == ID_object_address && rhs_p.id() == ID_object_address)
      {
        if(
          to_object_address_expr(lhs_p).object_identifier() ==
          to_object_address_expr(rhs_p).object_identifier())
          return true_exprt();
        else
          return false_exprt();
      }
    }
  }

  return src;
}

exprt simplify_state_expr(
  exprt src,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns)
{
  // operands first, recursively
  for(auto &op : src.operands())
    op = simplify_state_expr(op, address_taken, ns);

  // now the node itself
  src = simplify_state_expr_node(src, address_taken, ns);

  return src;
}
