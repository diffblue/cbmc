/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "c_typecast.h"

#include <algorithm>

#include <cassert>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/expr_util.h>
#include <util/std_expr.h>
#include <util/base_type.h>
#include <util/symbol.h>
#include <util/simplify_expr.h>

#include "c_qualifiers.h"

bool c_implicit_typecast(
  exprt &expr,
  const typet &dest_type,
  const namespacet &ns)
{
  c_typecastt c_typecast(ns);
  c_typecast.implicit_typecast(expr, dest_type);
  return !c_typecast.errors.empty();
}

bool check_c_implicit_typecast(
  const typet &src_type,
  const typet &dest_type,
  const namespacet &ns)
{
  c_typecastt c_typecast(ns);
  exprt tmp;
  tmp.type()=src_type;
  c_typecast.implicit_typecast(tmp, dest_type);
  return !c_typecast.errors.empty();
}

/// perform arithmetic prompotions and conversions
bool c_implicit_typecast_arithmetic(
  exprt &expr1, exprt &expr2,
  const namespacet &ns)
{
  c_typecastt c_typecast(ns);
  c_typecast.implicit_typecast_arithmetic(expr1, expr2);
  return !c_typecast.errors.empty();
}

bool is_void_pointer(const typet &type)
{
  if(type.id()==ID_pointer)
  {
    if(type.subtype().id()==ID_empty)
      return true;

    return is_void_pointer(type.subtype());
  }
  else
    return false;
}

bool check_c_implicit_typecast(
  const typet &src_type,
  const typet &dest_type)
{
  // check qualifiers

  if(src_type.id()==ID_pointer && dest_type.id()==ID_pointer &&
     src_type.subtype().get_bool(ID_C_constant) &&
     !dest_type.subtype().get_bool(ID_C_constant))
    return true;

  if(src_type==dest_type)
    return false;

  const irep_idt &src_type_id=src_type.id();

  if(src_type_id==ID_c_bit_field)
    return check_c_implicit_typecast(src_type.subtype(), dest_type);

  if(dest_type.id()==ID_c_bit_field)
    return check_c_implicit_typecast(src_type, dest_type.subtype());

  if(src_type_id==ID_natural)
  {
    if(dest_type.id()==ID_bool ||
       dest_type.id()==ID_c_bool ||
       dest_type.id()==ID_integer ||
       dest_type.id()==ID_real ||
       dest_type.id()==ID_complex ||
       dest_type.id()==ID_unsignedbv ||
       dest_type.id()==ID_signedbv ||
       dest_type.id()==ID_floatbv ||
       dest_type.id()==ID_complex)
      return false;
  }
  else if(src_type_id==ID_integer)
  {
    if(dest_type.id()==ID_bool ||
       dest_type.id()==ID_c_bool ||
       dest_type.id()==ID_real ||
       dest_type.id()==ID_complex ||
       dest_type.id()==ID_unsignedbv ||
       dest_type.id()==ID_signedbv ||
       dest_type.id()==ID_floatbv ||
       dest_type.id()==ID_fixedbv ||
       dest_type.id()==ID_pointer ||
       dest_type.id()==ID_complex)
      return false;
  }
  else if(src_type_id==ID_real)
  {
    if(dest_type.id()==ID_bool ||
       dest_type.id()==ID_c_bool ||
       dest_type.id()==ID_complex ||
       dest_type.id()==ID_floatbv ||
       dest_type.id()==ID_fixedbv ||
       dest_type.id()==ID_complex)
      return false;
  }
  else if(src_type_id==ID_rational)
  {
    if(dest_type.id()==ID_bool ||
       dest_type.id()==ID_c_bool ||
       dest_type.id()==ID_complex ||
       dest_type.id()==ID_floatbv ||
       dest_type.id()==ID_fixedbv ||
       dest_type.id()==ID_complex)
      return false;
  }
  else if(src_type_id==ID_bool)
  {
    if(dest_type.id()==ID_c_bool ||
       dest_type.id()==ID_integer ||
       dest_type.id()==ID_real ||
       dest_type.id()==ID_unsignedbv ||
       dest_type.id()==ID_signedbv ||
       dest_type.id()==ID_pointer ||
       dest_type.id()==ID_floatbv ||
       dest_type.id()==ID_fixedbv ||
       dest_type.id()==ID_c_enum ||
       dest_type.id()==ID_c_enum_tag ||
       dest_type.id()==ID_complex)
      return false;
  }
  else if(src_type_id==ID_unsignedbv ||
          src_type_id==ID_signedbv ||
          src_type_id==ID_c_enum ||
          src_type_id==ID_c_enum_tag ||
          src_type_id==ID_c_bool)
  {
    if(dest_type.id()==ID_unsignedbv ||
       dest_type.id()==ID_bool ||
       dest_type.id()==ID_c_bool ||
       dest_type.id()==ID_integer ||
       dest_type.id()==ID_real ||
       dest_type.id()==ID_rational ||
       dest_type.id()==ID_signedbv ||
       dest_type.id()==ID_floatbv ||
       dest_type.id()==ID_fixedbv ||
       dest_type.id()==ID_pointer ||
       dest_type.id()==ID_c_enum ||
       dest_type.id()==ID_c_enum_tag ||
       dest_type.id()==ID_complex)
      return false;
  }
  else if(src_type_id==ID_floatbv ||
          src_type_id==ID_fixedbv)
  {
    if(dest_type.id()==ID_bool ||
       dest_type.id()==ID_c_bool ||
       dest_type.id()==ID_integer ||
       dest_type.id()==ID_real ||
       dest_type.id()==ID_rational ||
       dest_type.id()==ID_signedbv ||
       dest_type.id()==ID_unsignedbv ||
       dest_type.id()==ID_floatbv ||
       dest_type.id()==ID_fixedbv ||
       dest_type.id()==ID_complex)
      return false;
  }
  else if(src_type_id==ID_complex)
  {
    if(dest_type.id()==ID_complex)
      return check_c_implicit_typecast(src_type.subtype(), dest_type.subtype());
    else
    {
      // 6.3.1.7, par 2:

      // When a value of complex type is converted to a real type, the
      // imaginary part of the complex value is discarded and the value of the
      // real part is converted according to the conversion rules for the
      // corresponding real type.

      return check_c_implicit_typecast(src_type.subtype(), dest_type);
    }
  }
  else if(src_type_id==ID_array ||
          src_type_id==ID_pointer)
  {
    if(dest_type.id()==ID_pointer)
    {
      const irept &dest_subtype=dest_type.subtype();
      const irept &src_subtype =src_type.subtype();

      if(src_subtype==dest_subtype)
        return false;
      else if(is_void_pointer(src_type) || // from void to anything
              is_void_pointer(dest_type))  // to void from anything
        return false;
    }

    if(dest_type.id()==ID_array &&
       src_type.subtype()==dest_type.subtype())
      return false;

    if(dest_type.id()==ID_bool ||
       dest_type.id()==ID_c_bool ||
       dest_type.id()==ID_unsignedbv ||
       dest_type.id()==ID_signedbv)
      return false;
  }
  else if(src_type_id==ID_vector)
  {
    if(dest_type.id()==ID_vector)
      return false;
  }
  else if(src_type_id==ID_complex)
  {
    if(dest_type.id()==ID_complex)
    {
      // We convert between complex types if we convert between
      // their component types.
      if(!check_c_implicit_typecast(src_type.subtype(), dest_type.subtype()))
        return false;
    }
  }

  return true;
}

typet c_typecastt::follow_with_qualifiers(const typet &src_type)
{
  if(
    src_type.id() != ID_struct_tag &&
    src_type.id() != ID_union_tag)
  {
    return src_type;
  }

  typet result_type=src_type;

  // collect qualifiers
  c_qualifierst qualifiers(src_type);

  while(result_type.id() == ID_struct_tag || result_type.id() == ID_union_tag)
  {
    const typet &followed_type = ns.follow(result_type);
    result_type = followed_type;
    qualifiers += c_qualifierst(followed_type);
  }

  qualifiers.write(result_type);

  return result_type;
}

c_typecastt::c_typet c_typecastt::get_c_type(
  const typet &type) const
{
  if(type.id()==ID_signedbv)
  {
    const std::size_t width = to_bitvector_type(type).get_width();

    if(width<=config.ansi_c.char_width)
      return CHAR;
    else if(width<=config.ansi_c.short_int_width)
      return SHORT;
    else if(width<=config.ansi_c.int_width)
      return INT;
    else if(width<=config.ansi_c.long_int_width)
      return LONG;
    else if(width<=config.ansi_c.long_long_int_width)
      return LONGLONG;
    else
      return LARGE_SIGNED_INT;
  }
  else if(type.id()==ID_unsignedbv)
  {
    const std::size_t width = to_bitvector_type(type).get_width();

    if(width<=config.ansi_c.char_width)
      return UCHAR;
    else if(width<=config.ansi_c.short_int_width)
      return USHORT;
    else if(width<=config.ansi_c.int_width)
      return UINT;
    else if(width<=config.ansi_c.long_int_width)
      return ULONG;
    else if(width<=config.ansi_c.long_long_int_width)
      return ULONGLONG;
    else
      return LARGE_UNSIGNED_INT;
  }
  else if(type.id()==ID_bool)
    return BOOL;
  else if(type.id()==ID_c_bool)
    return BOOL;
  else if(type.id()==ID_floatbv)
  {
    const std::size_t width = to_bitvector_type(type).get_width();

    if(width<=config.ansi_c.single_width)
      return SINGLE;
    else if(width<=config.ansi_c.double_width)
      return DOUBLE;
    else if(width<=config.ansi_c.long_double_width)
      return LONGDOUBLE;
    else if(width<=128)
      return FLOAT128;
  }
  else if(type.id()==ID_fixedbv)
  {
    return FIXEDBV;
  }
  else if(type.id()==ID_pointer)
  {
    if(type.subtype().id()==ID_empty)
      return VOIDPTR;
    else
      return PTR;
  }
  else if(type.id()==ID_array)
  {
    return PTR;
  }
  else if(type.id() == ID_c_enum || type.id() == ID_c_enum_tag)
  {
    return INT;
  }
  else if(type.id()==ID_rational)
    return RATIONAL;
  else if(type.id()==ID_real)
    return REAL;
  else if(type.id()==ID_complex)
    return COMPLEX;
  else if(type.id()==ID_c_bit_field)
  {
    const auto &bit_field_type = to_c_bit_field_type(type);

    // We take the underlying type, and then apply the number
    // of bits given
    typet underlying_type;

    if(bit_field_type.subtype().id() == ID_c_enum_tag)
    {
      const auto &followed =
        ns.follow_tag(to_c_enum_tag_type(bit_field_type.subtype()));
      if(followed.is_incomplete())
        return INT;
      else
        underlying_type = followed.subtype();
    }
    else
      underlying_type = bit_field_type.subtype();

    const bitvector_typet new_type(
      underlying_type.id(), bit_field_type.get_width());

    return get_c_type(new_type);
  }

  return OTHER;
}

void c_typecastt::implicit_typecast_arithmetic(
  exprt &expr,
  c_typet c_type)
{
  typet new_type;

  switch(c_type)
  {
  case PTR:
    if(expr.type().id() == ID_array)
    {
      new_type = pointer_type(expr.type().subtype());
      break;
    }
    return;

  case BOOL:       UNREACHABLE; // should always be promoted to int
  case CHAR:       UNREACHABLE; // should always be promoted to int
  case UCHAR:      UNREACHABLE; // should always be promoted to int
  case SHORT:      UNREACHABLE; // should always be promoted to int
  case USHORT:     UNREACHABLE; // should always be promoted to int
  case INT:        new_type=signed_int_type(); break;
  case UINT:       new_type=unsigned_int_type(); break;
  case LONG:       new_type=signed_long_int_type(); break;
  case ULONG:      new_type=unsigned_long_int_type(); break;
  case LONGLONG:   new_type=signed_long_long_int_type(); break;
  case ULONGLONG:  new_type=unsigned_long_long_int_type(); break;
  case SINGLE:     new_type=float_type(); break;
  case DOUBLE:     new_type=double_type(); break;
  case LONGDOUBLE: new_type=long_double_type(); break;
  // NOLINTNEXTLINE(whitespace/line_length)
  case FLOAT128:   new_type=ieee_float_spect::quadruple_precision().to_type(); break;
  case RATIONAL:   new_type=rational_typet(); break;
  case REAL:       new_type=real_typet(); break;
  case INTEGER:    new_type=integer_typet(); break;
  case COMPLEX: return; // do nothing
  default: return;
  }

  if(new_type != expr.type())
    do_typecast(expr, new_type);
}

c_typecastt::c_typet c_typecastt::minimum_promotion(
  const typet &type) const
{
  c_typet c_type=get_c_type(type);

  // 6.3.1.1, par 2

  // "If an int can represent all values of the original type, the
  // value is converted to an int; otherwise, it is converted to
  // an unsigned int."

  c_typet max_type=std::max(c_type, INT); // minimum promotion

  // The second case can arise if we promote any unsigned type
  // that is as large as unsigned int. In this case the promotion configuration
  // via the enum is actually wrong, and we need to fix this up.
  if(
    config.ansi_c.short_int_width == config.ansi_c.int_width &&
    c_type == USHORT)
    max_type=UINT;
  else if(
    config.ansi_c.char_width == config.ansi_c.int_width && c_type == UCHAR)
    max_type=UINT;

  if(max_type==UINT &&
     type.id()==ID_c_bit_field &&
     to_c_bit_field_type(type).get_width()<config.ansi_c.int_width)
    max_type=INT;

  return max_type;
}

void c_typecastt::implicit_typecast_arithmetic(exprt &expr)
{
  c_typet c_type=minimum_promotion(expr.type());
  implicit_typecast_arithmetic(expr, c_type);
}

void c_typecastt::implicit_typecast(
  exprt &expr,
  const typet &type)
{
  typet src_type=follow_with_qualifiers(expr.type()),
        dest_type=follow_with_qualifiers(type);

  typet type_qual=type;
  c_qualifierst qualifiers(dest_type);
  qualifiers.write(type_qual);

  implicit_typecast_followed(expr, src_type, type_qual, dest_type);
}

void c_typecastt::implicit_typecast_followed(
  exprt &expr,
  const typet &src_type,
  const typet &orig_dest_type,
  const typet &dest_type)
{
  // do transparent union
  if(dest_type.id()==ID_union &&
     dest_type.get_bool(ID_C_transparent_union) &&
     src_type.id()!=ID_union)
  {
    // The argument corresponding to a transparent union type can be of any
    // type in the union; no explicit cast is required.

    // GCC docs say:
    //  If the union member type is a pointer, qualifiers like const on the
    //  referenced type must be respected, just as with normal pointer
    //  conversions.
    // But it is accepted, and Clang doesn't even emit a warning (GCC 4.7 does)
    typet src_type_no_const=src_type;
    if(src_type.id()==ID_pointer &&
       src_type.subtype().get_bool(ID_C_constant))
      src_type_no_const.subtype().remove(ID_C_constant);

    // Check union members.
    for(const auto &comp : to_union_type(dest_type).components())
    {
      if(!check_c_implicit_typecast(src_type_no_const, comp.type()))
      {
        // build union constructor
        union_exprt union_expr(comp.get_name(), expr, orig_dest_type);
        if(!src_type.full_eq(src_type_no_const))
          do_typecast(union_expr.op(), src_type_no_const);
        expr=union_expr;
        return; // ok
      }
    }
  }

  if(dest_type.id()==ID_pointer)
  {
    // special case: 0 == NULL

    if(simplify_expr(expr, ns).is_zero() && (
       src_type.id()==ID_unsignedbv ||
       src_type.id()==ID_signedbv ||
       src_type.id()==ID_natural ||
       src_type.id()==ID_integer))
    {
      expr=exprt(ID_constant, orig_dest_type);
      expr.set(ID_value, ID_NULL);
      return; // ok
    }

    if(src_type.id()==ID_pointer ||
       src_type.id()==ID_array)
    {
      // we are quite generous about pointers

      const typet &src_sub = src_type.subtype();
      const typet &dest_sub = dest_type.subtype();

      if(is_void_pointer(src_type) ||
         is_void_pointer(dest_type))
      {
        // from/to void is always good
      }
      else if(src_sub.id()==ID_code &&
              dest_sub.id()==ID_code)
      {
        // very generous:
        // between any two function pointers it's ok
      }
      else if(base_type_eq(src_sub, dest_sub, ns))
      {
        // ok
      }
      else if((is_number(src_sub) ||
               src_sub.id()==ID_c_enum ||
               src_sub.id()==ID_c_enum_tag) &&
              (is_number(dest_sub) ||
               dest_sub.id()==ID_c_enum ||
               src_sub.id()==ID_c_enum_tag))
      {
        // Also generous: between any to scalar types it's ok.
        // We should probably check the size.
      }
      else if(src_sub.id()==ID_array &&
              dest_sub.id()==ID_array &&
              base_type_eq(src_sub.subtype(), dest_sub.subtype(), ns))
      {
        // we ignore the size of the top-level array
        // in the case of pointers to arrays
      }
      else
        warnings.push_back("incompatible pointer types");

      // check qualifiers

      if(src_type.subtype().get_bool(ID_C_volatile) &&
         !dest_type.subtype().get_bool(ID_C_volatile))
        warnings.push_back("disregarding volatile");

      if(src_type==dest_type)
      {
        expr.type()=src_type; // because of qualifiers
      }
      else
        do_typecast(expr, orig_dest_type);

      return; // ok
    }
  }

  if(check_c_implicit_typecast(src_type, dest_type))
    errors.push_back("implicit conversion not permitted");
  else if(src_type!=dest_type)
    do_typecast(expr, orig_dest_type);
}

void c_typecastt::implicit_typecast_arithmetic(
  exprt &expr1,
  exprt &expr2)
{
  const typet &type1 = expr1.type();
  const typet &type2 = expr2.type();

  c_typet c_type1=minimum_promotion(type1),
          c_type2=minimum_promotion(type2);

  c_typet max_type=std::max(c_type1, c_type2);

  if(max_type==LARGE_SIGNED_INT || max_type==LARGE_UNSIGNED_INT)
  {
    // get the biggest width of both
    std::size_t width1 = to_bitvector_type(type1).get_width();
    std::size_t width2 = to_bitvector_type(type2).get_width();

    // produce type
    typet result_type;

    if(width1==width2)
    {
      if(max_type==LARGE_SIGNED_INT)
        result_type=signedbv_typet(width1);
      else
        result_type=unsignedbv_typet(width1);
    }
    else if(width1>width2)
      result_type=type1;
    else // width1<width2
      result_type=type2;

    do_typecast(expr1, result_type);
    do_typecast(expr2, result_type);

    return;
  }
  else if(max_type==FIXEDBV)
  {
    typet result_type;

    if(c_type1==FIXEDBV && c_type2==FIXEDBV)
    {
      // get bigger of both
      std::size_t width1=to_fixedbv_type(type1).get_width();
      std::size_t width2=to_fixedbv_type(type2).get_width();
      if(width1>=width2)
        result_type=type1;
      else
        result_type=type2;
    }
    else if(c_type1==FIXEDBV)
      result_type=type1;
    else
      result_type=type2;

    do_typecast(expr1, result_type);
    do_typecast(expr2, result_type);

    return;
  }
  else if(max_type==COMPLEX)
  {
    if(c_type1==COMPLEX && c_type2==COMPLEX)
    {
      // promote to the one with bigger subtype
      if(get_c_type(type1.subtype())>get_c_type(type2.subtype()))
        do_typecast(expr2, type1);
      else
        do_typecast(expr1, type2);
    }
    else if(c_type1==COMPLEX)
    {
      assert(c_type1==COMPLEX && c_type2!=COMPLEX);
      do_typecast(expr2, type1.subtype());
      do_typecast(expr2, type1);
    }
    else
    {
      assert(c_type1!=COMPLEX && c_type2==COMPLEX);
      do_typecast(expr1, type2.subtype());
      do_typecast(expr1, type2);
    }

    return;
  }
  else if(max_type==SINGLE || max_type==DOUBLE ||
          max_type==LONGDOUBLE || max_type==FLOAT128)
  {
    // Special-case optimisation:
    // If we have two non-standard sized floats, don't do implicit type
    // promotion if we can possibly avoid it.
    if(type1==type2)
      return;
  }

  implicit_typecast_arithmetic(expr1, max_type);
  implicit_typecast_arithmetic(expr2, max_type);

  // arithmetic typecasts only, otherwise this can't be used from
  // typecheck_expr_trinary
  #if 0
  if(max_type==PTR)
  {
    if(c_type1==VOIDPTR)
      do_typecast(expr1, expr2.type());

    if(c_type2==VOIDPTR)
      do_typecast(expr2, expr1.type());
  }
  #endif
}

void c_typecastt::do_typecast(exprt &expr, const typet &dest_type)
{
  // special case: array -> pointer is actually
  // something like address_of

  const typet &src_type = expr.type();

  if(src_type.id()==ID_array)
  {
    index_exprt index;
    index.array()=expr;
    index.index()=from_integer(0, index_type());
    index.type()=src_type.subtype();
    expr = typecast_exprt::conditional_cast(address_of_exprt(index), dest_type);
    return;
  }

  if(src_type!=dest_type)
  {
    // C booleans are special; we produce the
    // explicit comparison with zero.
    // Note that this requires ieee_float_notequal
    // in case of floating-point numbers.

    if(dest_type.get(ID_C_c_type)==ID_bool)
    {
      expr=is_not_zero(expr, ns);
      expr.make_typecast(dest_type);
    }
    else if(dest_type.id()==ID_bool)
    {
      expr=is_not_zero(expr, ns);
    }
    else
    {
      expr.make_typecast(dest_type);
    }
  }
}
