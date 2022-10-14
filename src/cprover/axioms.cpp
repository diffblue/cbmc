/*******************************************************************\

Module: Axioms

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Axioms

#include "axioms.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/c_types.h>
#include <util/format_expr.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/string_constant.h>
#include <util/symbol.h>

#include "simplify_state_expr.h"

#include <iostream>

void axiomst::set_to_true(exprt src)
{
  constraints.push_back(std::move(src));
}

void axiomst::set_to_false(exprt src)
{
  set_to_true(not_exprt(src));
}

typet axiomst::replace(typet src)
{
  if(src.id() == ID_array)
  {
    auto &array_type = to_array_type(src);
    array_type.element_type() = replace(array_type.element_type());
    array_type.size() = replace(array_type.size());
    return src;
  }
  else if(src.id() == ID_pointer)
  {
    to_pointer_type(src).base_type() =
      replace(to_pointer_type(src).base_type());
    return src;
  }
  else
    return src;
}

void axiomst::evaluate_fc()
{
  // quadratic
  for(auto a_it = evaluate_exprs.begin(); a_it != evaluate_exprs.end(); a_it++)
  {
    for(auto b_it = std::next(a_it); b_it != evaluate_exprs.end(); b_it++)
    {
      if(a_it->state() != b_it->state())
        continue;

      auto a_op = a_it->address();
      auto b_op = typecast_exprt::conditional_cast(
        b_it->address(), a_it->address().type());
      auto operands_equal = equal_exprt(a_op, b_op);
      auto implication = implies_exprt(
        operands_equal,
        equal_exprt(
          *a_it, typecast_exprt::conditional_cast(*b_it, a_it->type())));
#if 0
      if(verbose)
        std::cout << "EVALUATE: " << format(implication) << '\n';
#endif
      dest << replace(implication);
    }
  }
}

void axiomst::is_cstring_fc()
{
  // quadratic
  for(auto a_it = is_cstring_exprs.begin(); a_it != is_cstring_exprs.end();
      a_it++)
  {
    for(auto b_it = std::next(a_it); b_it != is_cstring_exprs.end(); b_it++)
    {
      if(a_it->state() != b_it->state())
        continue;
      auto a_op = a_it->address();
      auto b_op = typecast_exprt::conditional_cast(
        b_it->address(), a_it->address().type());
      auto operands_equal = equal_exprt(a_op, b_op);
      auto implication =
        implies_exprt(operands_equal, equal_exprt(*a_it, *b_it));
      if(verbose)
        std::cout << "IS_CSTRING: " << format(implication) << '\n';
      dest << replace(implication);
    }
  }
}

void axiomst::live_object()
{
  // p = &"string_literal" -> live_object(ς, p)
  for(auto a_it = live_object_exprs.begin(); a_it != live_object_exprs.end();
      a_it++)
  {
    for(auto b_it = address_of_exprs.begin(); b_it != address_of_exprs.end();
        b_it++)
    {
      auto pointers_equal = same_object(a_it->address(), *b_it);
      auto implication = implies_exprt(pointers_equal, *a_it);
      if(verbose)
        std::cout << "LIVE_OBJECT2: " << format(implication) << '\n';
      dest << replace(implication);
    }
  }
}

void axiomst::live_object_fc()
{
  // quadratic
  for(auto a_it = live_object_exprs.begin(); a_it != live_object_exprs.end();
      a_it++)
  {
    for(auto b_it = std::next(a_it); b_it != live_object_exprs.end(); b_it++)
    {
      if(a_it->state() != b_it->state())
        continue;
      auto operands_equal = same_object(a_it->address(), b_it->address());
      auto implication =
        implies_exprt(operands_equal, equal_exprt(*a_it, *b_it));
      if(verbose)
        std::cout << "LIVE_OBJECT1: " << format(implication) << '\n';
      dest << replace(implication);
    }
  }
}

void axiomst::writeable_object()
{
  // p = &"string_literal" -> !writeable_object(ς, p)
  for(auto a_it = writeable_object_exprs.begin();
      a_it != writeable_object_exprs.end();
      a_it++)
  {
    for(auto b_it = address_of_exprs.begin(); b_it != address_of_exprs.end();
        b_it++)
    {
      auto pointers_equal = same_object(a_it->address(), *b_it);
      auto implication = implies_exprt(pointers_equal, not_exprt(*a_it));
      if(verbose)
        std::cout << "WRITEABLE_OBJECT2: " << format(implication) << '\n';
      dest << replace(implication);
    }
  }

  // p = &some_object -> writeable_object(ς, p)  as applicable
  for(auto a_it = object_address_exprs.begin();
      a_it != object_address_exprs.end();
      a_it++)
  {
    if(a_it->object_identifier() == "return_value")
      continue;
    else if(has_prefix(id2string(a_it->object_identifier()), "va_args::"))
      continue;
    else if(has_prefix(id2string(a_it->object_identifier()), "va_arg::"))
      continue;
    else if(has_prefix(id2string(a_it->object_identifier()), "va_arg_array::"))
      continue;
    else if(has_prefix(id2string(a_it->object_identifier()), "old::"))
      continue;

    auto &symbol = ns.lookup(a_it->object_expr());
    bool is_const = symbol.type.get_bool(ID_C_constant);
    for(auto b_it = writeable_object_exprs.begin();
        b_it != writeable_object_exprs.end();
        b_it++)
    {
      auto pointers_equal = same_object(*a_it, b_it->address());
      auto rhs = is_const ? static_cast<exprt>(not_exprt(*b_it))
                          : static_cast<exprt>(*b_it);
      auto implication = implies_exprt(pointers_equal, rhs);
      if(verbose)
        std::cout << "WRITEABLE_OBJECT3: " << format(implication) << '\n';
      dest << replace(implication);
    }
  }
}

void axiomst::writeable_object_fc()
{
  // quadratic
  for(auto a_it = writeable_object_exprs.begin();
      a_it != writeable_object_exprs.end();
      a_it++)
  {
    for(auto b_it = std::next(a_it); b_it != writeable_object_exprs.end();
        b_it++)
    {
      if(a_it->state() != b_it->state())
        continue;
      auto operands_equal = same_object(a_it->address(), b_it->address());
      auto implication =
        implies_exprt(operands_equal, equal_exprt(*a_it, *b_it));
      if(verbose)
        std::cout << "WRITEABLE_OBJECT1: " << format(implication) << '\n';
      dest << replace(implication);
    }
  }
}

void axiomst::is_dynamic_object_fc()
{
  // quadratic
  for(auto a_it = is_dynamic_object_exprs.begin();
      a_it != is_dynamic_object_exprs.end();
      a_it++)
  {
    for(auto b_it = std::next(a_it); b_it != is_dynamic_object_exprs.end();
        b_it++)
    {
      if(a_it->state() != b_it->state())
        continue;
      auto operands_equal = same_object(a_it->address(), b_it->address());
      auto implication =
        implies_exprt(operands_equal, equal_exprt(*a_it, *b_it));
      if(verbose)
        std::cout << "IS_DYNAMIC_OBJECT: " << format(implication) << '\n';
      dest << replace(implication);
    }
  }
}

void axiomst::object_size()
{
  for(const auto &src : object_size_exprs)
  {
    auto src_simplified = simplify_state_expr_node(src, address_taken, ns);
    if(src_simplified != src)
    {
      auto equal = equal_exprt(src, src_simplified);
      if(verbose)
        std::cout << "OBJECT_SIZE1: " << format(equal) << '\n';
      dest << replace(equal);
    }
  }

  // p = &"string_literal" -> object_size(ς, p) = strlen("string_literal")+1
  for(auto a_it = object_size_exprs.begin(); a_it != object_size_exprs.end();
      a_it++)
  {
    for(auto b_it = address_of_exprs.begin(); b_it != address_of_exprs.end();
        b_it++)
    {
      if(b_it->object().id() == ID_string_constant)
      {
        auto &string_constant = to_string_constant(b_it->object());
        auto pointers_equal = same_object(a_it->address(), *b_it);
        auto size_equal = equal_exprt(
          *a_it,
          from_integer(string_constant.get_value().size() + 1, a_it->type()));
        auto implication = implies_exprt(pointers_equal, size_equal);
        if(verbose)
          std::cout << "OBJECT_SIZE2: " << format(implication) << '\n';
        dest << replace(implication);
      }
    }
  }
}

void axiomst::object_size_fc()
{
  // quadratic
  for(auto a_it = object_size_exprs.begin(); a_it != object_size_exprs.end();
      a_it++)
  {
    for(auto b_it = std::next(a_it); b_it != object_size_exprs.end(); b_it++)
    {
      if(a_it->state() != b_it->state())
        continue;
      auto operands_equal = same_object(a_it->address(), b_it->address());
      auto implication =
        implies_exprt(operands_equal, equal_exprt(*a_it, *b_it));
      if(verbose)
        std::cout << "OBJECT_SIZE: " << format(implication) << '\n';
      dest << replace(implication);
    }
  }
}

void axiomst::ok_fc()
{
  // quadratic
  for(auto a_it = ok_exprs.begin(); a_it != ok_exprs.end(); a_it++)
  {
    for(auto b_it = std::next(a_it); b_it != ok_exprs.end(); b_it++)
    {
      if(a_it->id() != b_it->id())
        continue;
      if(a_it->state() != b_it->state())
        continue;
      if(a_it->size() != b_it->size())
        continue;
      auto a_op = a_it->address();
      auto b_op = typecast_exprt::conditional_cast(
        b_it->address(), a_it->address().type());
      auto operands_equal = equal_exprt(a_op, b_op);
      auto implication =
        implies_exprt(operands_equal, equal_exprt(*a_it, *b_it));
      if(verbose)
        std::cout << "OK: " << format(implication) << '\n';
      dest << replace(implication);
    }
  }
}

void axiomst::initial_state()
{
  for(const auto &initial_state_expr : initial_state_exprs)
  {
    // initial_state(ς) -> ¬live_object(ς, o)   for any stack-allocated object o
    for(const auto &object : address_taken)
    {
      const symbolt *symbol;
      if(ns.lookup(object.get_identifier(), symbol))
        continue;

      if(symbol->is_static_lifetime || !symbol->is_lvalue)
        continue;

      auto live_object = state_live_object_exprt(
        initial_state_expr.op(), object_address_exprt(object));
      live_object_exprs.insert(live_object);
      auto implication =
        implies_exprt(initial_state_expr, not_exprt(live_object));
      if(verbose)
        std::cout << "INITIAL_STATE: " << format(implication) << '\n';
      dest << replace(implication);
    }
  }
}

exprt axiomst::translate(exprt src) const
{
  auto r = replacement_map.find(src);
  if(r == replacement_map.end())
    return src;
  else
    return r->second;
}

exprt axiomst::replace(exprt src)
{
  src.type() = replace(src.type());

  if(
    src.id() == ID_initial_state || src.id() == ID_evaluate ||
    src.id() == ID_state_is_cstring || src.id() == ID_state_cstrlen ||
    src.id() == ID_state_is_sentinel_dll ||
    src.id() == ID_state_is_dynamic_object ||
    src.id() == ID_state_object_size || src.id() == ID_state_live_object ||
    src.id() == ID_state_writeable_object || src.id() == ID_state_r_ok ||
    src.id() == ID_state_w_ok || src.id() == ID_state_rw_ok ||
    src.id() == ID_allocate || src.id() == ID_reallocate)
  {
    auto r = replacement_map.find(src);
    if(r == replacement_map.end())
    {
      auto counter = ++counters[src.id()];
      auto s =
        symbol_exprt(src.id_string() + std::to_string(counter), src.type());
      replacement_map.emplace(src, s);

      if(src.id() == ID_state_is_cstring)
      {
        if(verbose)
          std::cout << "R " << format(s) << " --> " << format(src) << '\n';
      }

      return std::move(s);
    }
    else
      return r->second;
  }

  for(auto &op : src.operands())
    op = replace(op);

  return src;
}

void axiomst::node(const exprt &src)
{
  if(src.id() == ID_state_is_cstring)
  {
    add(to_state_is_cstring_expr(src), false);
  }
  else if(src.id() == ID_state_is_sentinel_dll)
  {
    auto &is_sentinel_dll_expr = to_state_is_sentinel_dll_expr(src);
    is_sentinel_dll_exprs.insert(is_sentinel_dll_expr);

    auto ok_expr_h_size_opt = size_of_expr(
      to_pointer_type(is_sentinel_dll_expr.head().type()).base_type(), ns);

    auto ok_expr_h = state_ok_exprt(
      ID_state_rw_ok,
      is_sentinel_dll_expr.state(),
      is_sentinel_dll_expr.head(),
      *ok_expr_h_size_opt);

    auto ok_expr_t_size_opt = size_of_expr(
      to_pointer_type(is_sentinel_dll_expr.tail().type()).base_type(), ns);

    auto ok_expr_t = state_ok_exprt(
      ID_state_rw_ok,
      is_sentinel_dll_expr.state(),
      is_sentinel_dll_expr.tail(),
      *ok_expr_t_size_opt);

    {
      // is_sentinel_dll(ς, h, t) ⇒ rw_ok(ς, h) ∧ rw_ok(ς, t)
      auto instance1 =
        replace(implies_exprt(src, and_exprt(ok_expr_h, ok_expr_t)));
      if(verbose)
        std::cout << "AXIOM-is-sentinel-dll-1: " << format(instance1) << "\n";
      dest << instance1;
    }

    {
      // rw_ok(h) ∧ rw_ok(t) ∧ ς(h->n)=t ∧ ς(t->p)=h ⇒ is_sentinel_dll(ς, h, t)
      auto head_next = sentinel_dll_next(
        is_sentinel_dll_expr.state(), is_sentinel_dll_expr.head(), ns);

      auto tail_prev = sentinel_dll_prev(
        is_sentinel_dll_expr.state(), is_sentinel_dll_expr.tail(), ns);

      if(head_next.has_value() && tail_prev.has_value())
      {
        auto head_next_is_tail =
          equal_exprt(*head_next, is_sentinel_dll_expr.tail());

        auto tail_prev_is_head =
          equal_exprt(*tail_prev, is_sentinel_dll_expr.head());

        auto instance2 = replace(implies_exprt(
          and_exprt(
            ok_expr_h, ok_expr_t /*, head_next_is_tail, tail_prev_is_head*/),
          src));

        if(verbose)
          std::cout << "AXIOM-is-sentinel-dll-2: " << format(instance2) << "\n";
        dest << instance2;
      }
    }
  }
  else if(src.id() == ID_evaluate)
  {
    const auto &evaluate_expr = to_evaluate_expr(src);
    evaluate_exprs.insert(evaluate_expr);
  }
  else if(src.id() == ID_state_live_object)
  {
    const auto &live_object_expr = to_state_live_object_expr(src);
    live_object_exprs.insert(live_object_expr);

    {
      // live_object(ς, p) --> p!=0
      auto instance = replace(implies_exprt(
        src, not_exprt(null_pointer(live_object_expr.address()))));
      if(verbose)
        std::cout << "AXIOMc: " << format(instance) << "\n";
      dest << instance;
    }
  }
  else if(src.id() == ID_state_writeable_object)
  {
    const auto &writeable_object_expr = to_state_writeable_object_expr(src);
    writeable_object_exprs.insert(writeable_object_expr);
  }
  else if(src.id() == ID_state_is_dynamic_object)
  {
    const auto &is_dynamic_object_expr = to_state_is_dynamic_object_expr(src);
    is_dynamic_object_exprs.insert(is_dynamic_object_expr);
  }
  else if(src.id() == ID_allocate)
  {
    const auto &allocate_expr = to_allocate_expr(src);

    // May need to consider failure.
    // live_object(ς, allocate(ς, s))
    auto live_object_expr =
      state_live_object_exprt(allocate_expr.state(), allocate_expr);
    live_object_exprs.insert(live_object_expr);
    auto instance1 = replace(live_object_expr);
    if(verbose)
      std::cout << "ALLOCATE1: " << format(instance1) << "\n";
    dest << instance1;

    // writeable_object(ς, allocate(ς, s))
    auto writeable_object_expr =
      state_writeable_object_exprt(allocate_expr.state(), allocate_expr);
    writeable_object_exprs.insert(writeable_object_expr);
    auto instance2 = replace(writeable_object_expr);
    if(verbose)
      std::cout << "ALLOCATE2: " << format(instance2) << "\n";
    dest << instance2;

    // object_size(ς, allocate(ς, s)) = s
    auto object_size_expr = state_object_size_exprt(
      allocate_expr.state(), allocate_expr, allocate_expr.size().type());
    object_size_exprs.insert(object_size_expr);
    auto instance3 =
      replace(equal_exprt(object_size_expr, allocate_expr.size()));
    if(verbose)
      std::cout << "ALLOCATE3: " << format(instance3) << "\n";
    dest << instance3;

    // pointer_offset(allocate(ς, s)) = 0
    auto pointer_offset_expr = pointer_offset(allocate_expr);
    // pointer_offset_exprs.insert(pointer_offset_expr);
    auto instance4 = replace(equal_exprt(
      pointer_offset_expr, from_integer(0, pointer_offset_expr.type())));
    if(verbose)
      std::cout << "ALLOCATE4: " << format(instance4) << "\n";
    dest << instance4;

    // is_dynamic_object(ς, allocate(ς, s))
    auto is_dynamic_object_expr =
      state_is_dynamic_object_exprt(allocate_expr.state(), allocate_expr);
    is_dynamic_object_exprs.insert(is_dynamic_object_expr);
    auto instance5 = replace(is_dynamic_object_expr);
    if(verbose)
      std::cout << "ALLOCATE5: " << format(instance5) << "\n";
    dest << instance5;
  }
  else if(src.id() == ID_reallocate)
  {
    const auto &reallocate_expr = to_reallocate_expr(src);

    // May need to consider failure.
    // live_object(ς, reallocate(ς, a, s))
    auto live_object_expr =
      state_live_object_exprt(reallocate_expr.state(), reallocate_expr);
    live_object_exprs.insert(live_object_expr);
    auto instance1 = replace(live_object_expr);
    if(verbose)
      std::cout << "REALLOCATE1: " << format(instance1) << "\n";
    dest << instance1;

    // object_size(ς, reallocate(ς, a, s)) = s
    auto object_size_expr = state_object_size_exprt(
      reallocate_expr.state(), reallocate_expr, reallocate_expr.size().type());
    object_size_exprs.insert(object_size_expr);
    auto instance2 =
      replace(equal_exprt(object_size_expr, reallocate_expr.size()));
    if(verbose)
      std::cout << "REALLOCATE2: " << format(instance2) << "\n";
    dest << instance2;

    // pointer_offset(reallocate(ς, a, s)) = 0
    auto pointer_offset_expr = pointer_offset(reallocate_expr);
    // pointer_offset_exprs.insert(pointer_offset_expr);
    auto instance3 = replace(equal_exprt(
      pointer_offset_expr, from_integer(0, pointer_offset_expr.type())));
    if(verbose)
      std::cout << "REALLOCATE3: " << format(instance3) << "\n";
    dest << instance3;

    // is_dynamic_object(ς, reallocate(ς, s))
    auto is_dynamic_object_expr =
      state_is_dynamic_object_exprt(reallocate_expr.state(), reallocate_expr);
    is_dynamic_object_exprs.insert(is_dynamic_object_expr);
    auto instance4 = replace(is_dynamic_object_expr);
    if(verbose)
      std::cout << "REALLOCATE4: " << format(instance4) << "\n";
    dest << instance4;
  }
  else if(src.id() == ID_deallocate_state)
  {
#if 0
    // Disabled since any other thread may have reclaimed
    // the memory.
    const auto &deallocate_state_expr = to_deallocate_state_expr(src);

    // ¬live_object(deallocate(ς, p), p)
    auto live_object_expr = state_live_object_exprt(
      deallocate_state_expr, deallocate_state_expr.address());
    live_object_exprs.insert(live_object_expr);
    auto instance1 = replace(not_exprt(live_object_expr));
    if(verbose)
      std::cout << "DEALLOCATE1: " << format(instance1) << "\n";
    dest << instance1;
#endif
  }
  else if(src.id() == ID_address_of)
  {
    address_of_exprs.insert(to_address_of_expr(src));
  }
  else if(src.id() == ID_object_address)
  {
    object_address_exprs.insert(to_object_address_expr(src));
  }
  else if(src.id() == ID_state_object_size)
  {
    const auto &object_size_expr = to_state_object_size_expr(src);
    object_size_exprs.insert(object_size_expr);
  }
  else if(src.id() == ID_initial_state)
  {
    initial_state_exprs.insert(to_initial_state_expr(src));
  }
  else if(
    src.id() == ID_state_r_ok || src.id() == ID_state_w_ok ||
    src.id() == ID_state_rw_ok)
  {
    add(to_state_ok_expr(src));
  }
}

void axiomst::add(const state_ok_exprt &ok_expr)
{
  if(!ok_exprs.insert(ok_expr).second)
    return; // already there

  const auto &state = ok_expr.state();
  const auto &pointer = ok_expr.address();
  const auto &size = ok_expr.size();

  {
    // X_ok(p, s) <-->
    //   live_object(p)
    // ∧ offset(p)+s≤object_size(p)
    // ∧ writeable_object(p)           if applicable
    auto live_object = state_live_object_exprt(state, pointer);
    live_object_exprs.insert(live_object);
    auto live_object_simplified =
      simplify_state_expr_node(live_object, address_taken, ns);

    auto writeable_object = state_writeable_object_exprt(state, pointer);
    writeable_object_exprs.insert(writeable_object);

    auto writeable_object_simplified =
      simplify_state_expr_node(writeable_object, address_taken, ns);

    auto ssize_type = signed_size_type();
    auto offset = pointer_offset_exprt(pointer, ssize_type);
    auto offset_simplified =
      simplify_state_expr_node(offset, address_taken, ns);
    //      auto lower = binary_relation_exprt(
    //        offset_simplified, ID_ge, from_integer(0, ssize_type));

    auto size_type = ::size_type();

    // extend one bit, to cover overflow case
    auto size_type_ext = unsignedbv_typet(size_type.get_width() + 1);

    auto object_size = state_object_size_exprt(state, pointer, size_type);
    object_size_exprs.insert(object_size);

    auto object_size_casted = typecast_exprt(object_size, size_type_ext);

    auto offset_casted_to_unsigned =
      typecast_exprt::conditional_cast(offset_simplified, size_type);
    auto offset_extended = typecast_exprt::conditional_cast(
      offset_casted_to_unsigned, size_type_ext);
    auto size_casted = typecast_exprt::conditional_cast(size, size_type_ext);
    auto upper = binary_relation_exprt(
      plus_exprt(offset_extended, size_casted), ID_le, object_size_casted);

    auto conjunction = and_exprt(live_object_simplified, upper);

    if(ok_expr.id() == ID_state_w_ok || ok_expr.id() == ID_state_rw_ok)
      conjunction.add_to_operands(std::move(writeable_object));

    auto instance = replace(equal_exprt(ok_expr, conjunction));

    if(verbose)
      std::cout << "AXIOMd: " << format(instance) << "\n";
    dest << instance;
  }

  {
    // X_ok(ς, p) --> p!=0
    auto instance =
      replace(implies_exprt(ok_expr, not_exprt(null_pointer(pointer))));
    if(verbose)
      std::cout << "AXIOMe: " << format(instance) << "\n";
    dest << instance;
  }
}

void axiomst::add(const state_is_cstring_exprt &is_cstring_expr, bool recursive)
{
  if(!is_cstring_exprs.insert(is_cstring_expr).second)
    return; // already there

  {
    // is_cstring(ς, p) ⇒ r_ok(ς, p, 1)
    auto ok_expr = ternary_exprt(
      ID_state_r_ok,
      is_cstring_expr.state(),
      is_cstring_expr.address(),
      from_integer(1, size_type()),
      bool_typet());

    auto instance1 = replace(implies_exprt(is_cstring_expr, ok_expr));
    if(verbose)
      std::cout << "AXIOMa1: " << format(instance1) << "\n";
    dest << instance1;

    auto ok_simplified = simplify_state_expr(ok_expr, address_taken, ns);
    ok_simplified.visit_pre([this](const exprt &src) { node(src); });
    auto instance2 = replace(implies_exprt(is_cstring_expr, ok_simplified));
    if(verbose)
      std::cout << "AXIOMa2: " << format(instance2) << "\n";
    dest << instance2;
  }

  if(!recursive)
  {
    // is_cstring(ς, p) --> is_cstring(ς, p + 1) ∨ ς(p)=0
    auto state = is_cstring_expr.state();
    auto p = is_cstring_expr.address();
    auto one = from_integer(1, signed_size_type());
    auto p_plus_one = plus_exprt(p, one, is_cstring_expr.op1().type());
    auto is_cstring_plus_one = state_is_cstring_exprt(state, p_plus_one);
    auto char_type = to_pointer_type(p.type()).base_type();
    auto zero = from_integer(0, char_type);
    auto star_p = evaluate_exprt(state, p, char_type);
    auto is_zero = equal_exprt(star_p, zero);
    auto instance = replace(
      implies_exprt(is_cstring_expr, or_exprt(is_cstring_plus_one, is_zero)));
    if(verbose)
      std::cout << "AXIOMb: " << format(instance) << "\n";
    dest << instance;
    evaluate_exprs.insert(star_p);
    add(is_cstring_plus_one, true); // rec. call
  }
}

void axiomst::emit()
{
  for(auto &constraint : constraints)
  {
    constraint.visit_pre([this](const exprt &src) { node(src); });

    auto constraint_replaced = replace(constraint);
#if 0
    if(verbose)
    {
      std::cout << "CONSTRAINT1: " << format(constraint) << "\n";
      std::cout << "CONSTRAINT2: " << format(constraint_replaced) << "\n";
    }
#endif
    dest << constraint_replaced;
  }

  object_size();
  live_object();
  writeable_object();
  initial_state();

  // functional consistency is done last
  evaluate_fc();
  is_cstring_fc();
  ok_fc();
  live_object_fc();
  writeable_object_fc();
  object_size_fc();
  is_dynamic_object_fc();
}
