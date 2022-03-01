/*******************************************************************\

Module: Solver

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// May Alias

#include "may_alias.h"

#include <util/c_types.h>
#include <util/format_expr.h>
#include <util/format_type.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/prefix.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <iostream>

bool permitted_by_strict_aliasing(const typet &a, const typet &b)
{
  // C99; ISO/IEC 9899:1999 6.5/7
  if(a == b)
    return true;
  else if(a == signed_char_type() || a == unsigned_char_type())
    return true; // char * can alias anyting
  else if(b == signed_char_type() || b == unsigned_char_type())
    return true; // char * can alias anyting
  else if(
    (a.id() == ID_unsignedbv || a.id() == ID_signedbv) &&
    (b.id() == ID_unsignedbv || b.id() == ID_signedbv))
  {
    // signed/unsigned of same width can alias
    return to_bitvector_type(a).get_width() == to_bitvector_type(b).get_width();
  }
  else if(a.id() == ID_empty)
    return true; // void * can alias any pointer
  else if(b.id() == ID_empty)
    return true; // void * can alias any pointer
  else if(
    a.id() == ID_pointer && to_pointer_type(a).base_type().id() == ID_empty)
    return true; // void * can alias any pointer
  else if(
    b.id() == ID_pointer && to_pointer_type(b).base_type().id() == ID_empty)
    return true; // void * can alias any pointer
  else if(
    a.id() == ID_pointer && to_pointer_type(a).base_type().id() == ID_pointer &&
    to_pointer_type(to_pointer_type(a).base_type()).base_type().id() ==
      ID_empty)
    return true; // void * can alias any pointer
  else if(
    b.id() == ID_pointer && to_pointer_type(b).base_type().id() == ID_pointer &&
    to_pointer_type(to_pointer_type(b).base_type()).base_type().id() ==
      ID_empty)
    return true; // void * can alias any pointer
  else
  {
    return false;
  }
}

bool is_object_field_element(const exprt &expr)
{
  if(expr.id() == ID_object_address)
    return true;
  else if(expr.id() == ID_element_address)
    return is_object_field_element(to_element_address_expr(expr).base());
  else if(expr.id() == ID_field_address)
    return is_object_field_element(to_field_address_expr(expr).base());
  else
    return false;
}

bool prefix_of(const typet &a, const typet &b, const namespacet &ns)
{
  if(a == b)
    return true;

  if(a.id() == ID_struct_tag)
    return prefix_of(ns.follow_tag(to_struct_tag_type(a)), b, ns);

  if(b.id() == ID_struct_tag)
    return prefix_of(a, ns.follow_tag(to_struct_tag_type(b)), ns);

  if(a.id() != ID_struct || b.id() != ID_struct)
    return false;

  const auto &a_struct = to_struct_type(a);
  const auto &b_struct = to_struct_type(b);

  return a_struct.is_prefix_of(b_struct) || b_struct.is_prefix_of(a_struct);
}

static optionalt<object_address_exprt> find_object(const exprt &expr)
{
  if(expr.id() == ID_object_address)
    return to_object_address_expr(expr);
  else if(expr.id() == ID_field_address)
    return find_object(to_field_address_expr(expr).base());
  else if(expr.id() == ID_element_address)
    return find_object(to_element_address_expr(expr).base());
  else
    return {};
}

// Is 'expr' on the stack and it's address is not taken?
bool stack_and_not_dirty(
  const exprt &expr,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns)
{
  auto object = find_object(expr);
  if(object.has_value())
  {
    auto symbol_expr = object->object_expr();
    auto identifier = symbol_expr.get_identifier();
    if(has_prefix(id2string(identifier), "va_arg::"))
      return true; // on the stack, and might alias
    else if(has_prefix(id2string(identifier), "var_args::"))
      return false; // on the stack -- can take address?
    else if(has_prefix(id2string(identifier), "va_args::"))
      return false; // on the stack -- can take address?
    else if(has_prefix(id2string(identifier), "va_arg_array::"))
      return false; // on the stack -- can take address?
    else if(has_prefix(id2string(identifier), "old::"))
      return true; // on the stack, but can't take address
    else if(identifier == "return_value")
      return true; // on the stack, but can't take address
    const auto &symbol = ns.lookup(symbol_expr);
    return !symbol.is_static_lifetime &&
           address_taken.find(symbol_expr) == address_taken.end();
  }
  else
    return false;
}

static exprt drop_pointer_typecasts(exprt src)
{
  if(
    src.id() == ID_typecast &&
    to_typecast_expr(src).op().type().id() == ID_pointer)
    return drop_pointer_typecasts(to_typecast_expr(src).op());
  else
    return src;
}

optionalt<exprt>
same_address(const exprt &a, const exprt &b, const namespacet &ns)
{
  static const auto true_expr = true_exprt();
  static const auto false_expr = false_exprt();

  // syntactically the same?
  if(drop_pointer_typecasts(a) == drop_pointer_typecasts(b))
    return true_expr;

  // a and b are both object/field/element?
  if(is_object_field_element(a) && is_object_field_element(b))
  {
    if(a.id() == ID_object_address && b.id() == ID_object_address)
    {
      if(
        to_object_address_expr(a).object_identifier() ==
        to_object_address_expr(b).object_identifier())
      {
        return true_expr; // the same
      }
      else
        return false_expr; // different
    }
    else if(a.id() == ID_element_address && b.id() == ID_element_address)
    {
      const auto &a_element_address = to_element_address_expr(a);
      const auto &b_element_address = to_element_address_expr(b);

      // rec. call
      auto base_same_address =
        same_address(a_element_address.base(), b_element_address.base(), ns);

      CHECK_RETURN(base_same_address.has_value());

      if(base_same_address->is_false())
        return false_expr;
      else
      {
        return and_exprt(
          *base_same_address,
          equal_exprt(a_element_address.index(), b_element_address.index()));
      }
    }
    else if(a.id() == ID_field_address && b.id() == ID_field_address)
    {
      const auto &a_field_address = to_field_address_expr(a);
      const auto &b_field_address = to_field_address_expr(b);

      // structs can't alias unless one is a prefix of the other
      if(!prefix_of(
           a_field_address.type().base_type(),
           b_field_address.type().base_type(),
           ns))
      {
        return false_expr;
      }

      if(a_field_address.component_name() == b_field_address.component_name())
      {
        // rec. call
        return same_address(a_field_address.base(), b_field_address.base(), ns);
      }
      else
        return false_expr;
    }
    else
      return false_expr;
  }

  // don't know
  return {};
}

optionalt<exprt> may_alias(
  const exprt &a,
  const exprt &b,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns)
{
  PRECONDITION(a.type().id() == ID_pointer);
  PRECONDITION(b.type().id() == ID_pointer);

  static const auto true_expr = true_exprt();
  static const auto false_expr = false_exprt();

  // syntactically the same?
  if(drop_pointer_typecasts(a) == drop_pointer_typecasts(b))
    return true_expr;

  // consider the strict aliasing rule
  const auto &a_base = to_pointer_type(a.type()).base_type();
  const auto &b_base = to_pointer_type(b.type()).base_type();

  if(!permitted_by_strict_aliasing(a_base, b_base))
  {
    // The object is known to be different, because of strict aliasing.
    return false_expr;
  }

  // a and b the same addresses?
  auto same_address_opt = same_address(a, b, ns);
  if(same_address_opt.has_value())
    return same_address_opt;

  // is one of them stack-allocated and it's address is not taken?
  if(stack_and_not_dirty(a, address_taken, ns))
    return false_expr; // can't alias

  if(stack_and_not_dirty(b, address_taken, ns))
    return false_expr; // can't alias

  // we don't know
  return {};
}
