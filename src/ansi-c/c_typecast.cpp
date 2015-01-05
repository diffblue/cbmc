/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>

#include <cassert>

#include <util/config.h>
#include <util/expr_util.h>
#include <util/std_expr.h>
#include <util/base_type.h>
#include <util/symbol.h>
#include <util/simplify_expr.h>

#include "c_typecast.h"
#include "c_types.h"
#include "c_qualifiers.h"

/*******************************************************************\

Function: c_implicit_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool c_implicit_typecast(
  exprt &expr,
  const typet &dest_type,
  const namespacet &ns)
{
  c_typecastt c_typecast(ns);
  c_typecast.implicit_typecast(expr, dest_type);
  return !c_typecast.errors.empty();
}

/*******************************************************************\

Function: check_c_implicit_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: c_implicit_typecast_arithmetic

  Inputs:

 Outputs:

 Purpose: perform arithmetic prompotions and conversions

\*******************************************************************/

bool c_implicit_typecast_arithmetic(
  exprt &expr1, exprt &expr2,
  const namespacet &ns)
{
  c_typecastt c_typecast(ns);
  c_typecast.implicit_typecast_arithmetic(expr1, expr2);
  return !c_typecast.errors.empty();
}

/*******************************************************************\

Function: is_void_pointer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: check_c_implicit_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool check_c_implicit_typecast(
  const typet &src_type,
  const typet &dest_type)
{
  // check qualifiers  

  if(src_type.id()==ID_pointer && dest_type.id()==ID_pointer &&
     src_type.subtype().get_bool(ID_C_constant) &&
     !dest_type.subtype().get_bool(ID_C_constant))
    return true;

  if(src_type==dest_type) return false;
  
  const irep_idt &src_type_id=src_type.id();

  if(src_type_id==ID_c_bit_field)
    return check_c_implicit_typecast(src_type.subtype(), dest_type);

  if(dest_type.id()==ID_c_bit_field)
    return check_c_implicit_typecast(src_type, dest_type.subtype());

  if(src_type_id==ID_natural)
  {
    if(dest_type.id()==ID_bool) return false;
    if(dest_type.id()==ID_c_bool) return false;
    if(dest_type.id()==ID_integer) return false;
    if(dest_type.id()==ID_real) return false;
    if(dest_type.id()==ID_complex) return false;
    if(dest_type.id()==ID_unsignedbv) return false;
    if(dest_type.id()==ID_signedbv) return false;
    if(dest_type.id()==ID_floatbv) return false;
    if(dest_type.id()==ID_complex) return false;
  }
  else if(src_type_id==ID_integer)
  {
    if(dest_type.id()==ID_bool) return false;
    if(dest_type.id()==ID_c_bool) return false;
    if(dest_type.id()==ID_real) return false;
    if(dest_type.id()==ID_complex) return false;
    if(dest_type.id()==ID_unsignedbv) return false;
    if(dest_type.id()==ID_signedbv) return false;
    if(dest_type.id()==ID_floatbv) return false;
    if(dest_type.id()==ID_fixedbv) return false;
    if(dest_type.id()==ID_pointer) return false;
    if(dest_type.id()==ID_complex) return false;
  }
  else if(src_type_id==ID_real)
  {
    if(dest_type.id()==ID_bool) return false;
    if(dest_type.id()==ID_c_bool) return false;
    if(dest_type.id()==ID_complex) return false;
    if(dest_type.id()==ID_floatbv) return false;
    if(dest_type.id()==ID_fixedbv) return false;
    if(dest_type.id()==ID_complex) return false;
  }
  else if(src_type_id==ID_rational)
  {
    if(dest_type.id()==ID_bool) return false;
    if(dest_type.id()==ID_c_bool) return false;
    if(dest_type.id()==ID_complex) return false;
    if(dest_type.id()==ID_floatbv) return false;
    if(dest_type.id()==ID_fixedbv) return false;
    if(dest_type.id()==ID_complex) return false;
  }
  else if(src_type_id==ID_bool)
  {
    if(dest_type.id()==ID_c_bool) return false;
    if(dest_type.id()==ID_integer) return false;
    if(dest_type.id()==ID_real) return false;
    if(dest_type.id()==ID_unsignedbv) return false;
    if(dest_type.id()==ID_signedbv) return false;
    if(dest_type.id()==ID_pointer) return false;
    if(dest_type.id()==ID_floatbv) return false;
    if(dest_type.id()==ID_fixedbv) return false;
    if(dest_type.id()==ID_c_enum) return false;
    if(dest_type.id()==ID_c_enum_tag) return false;
    if(dest_type.id()==ID_complex) return false;
  }
  else if(src_type_id==ID_unsignedbv ||
          src_type_id==ID_signedbv ||
          src_type_id==ID_c_enum ||
          src_type_id==ID_c_enum_tag ||
          src_type_id==ID_incomplete_c_enum ||
          src_type_id==ID_c_bool)
  {
    if(dest_type.id()==ID_unsignedbv) return false;
    if(dest_type.id()==ID_bool) return false;
    if(dest_type.id()==ID_c_bool) return false;
    if(dest_type.id()==ID_integer) return false;
    if(dest_type.id()==ID_real) return false;
    if(dest_type.id()==ID_rational) return false;
    if(dest_type.id()==ID_signedbv) return false;
    if(dest_type.id()==ID_floatbv) return false;
    if(dest_type.id()==ID_fixedbv) return false;
    if(dest_type.id()==ID_pointer) return false;
    if(dest_type.id()==ID_c_enum) return false;
    if(dest_type.id()==ID_c_enum_tag) return false;
    if(dest_type.id()==ID_incomplete_c_enum) return false;
    if(dest_type.id()==ID_complex) return false;
  }
  else if(src_type_id==ID_floatbv ||
          src_type_id==ID_fixedbv)
  {
    if(dest_type.id()==ID_bool) return false;
    if(dest_type.id()==ID_c_bool) return false;
    if(dest_type.id()==ID_integer) return false;
    if(dest_type.id()==ID_real) return false;
    if(dest_type.id()==ID_rational) return false;
    if(dest_type.id()==ID_signedbv) return false;
    if(dest_type.id()==ID_unsignedbv) return false;
    if(dest_type.id()==ID_floatbv) return false;
    if(dest_type.id()==ID_fixedbv) return false;
    if(dest_type.id()==ID_complex) return false;
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
       src_type.subtype()==dest_type.subtype()) return false;

    if(dest_type.id()==ID_bool) return false;
    if(dest_type.id()==ID_c_bool) return false;
    if(dest_type.id()==ID_unsignedbv) return false;
    if(dest_type.id()==ID_signedbv) return false;
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

/*******************************************************************\

Function: c_typecastt::follow_with_qualifiers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet c_typecastt::follow_with_qualifiers(const typet &src_type)
{
  if(src_type.id()!=ID_symbol) return src_type;
  
  typet result_type=src_type;
  
  // collect qualifiers
  c_qualifierst qualifiers(src_type);
  
  while(result_type.id()==ID_symbol)
  {
    const symbolt &followed_type_symbol=
      ns.lookup(result_type.get(ID_identifier));

    result_type=followed_type_symbol.type;
    qualifiers+=c_qualifierst(followed_type_symbol.type);
  }

  qualifiers.write(result_type);

  return result_type;
}

/*******************************************************************\

Function: c_typecastt::get_c_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

c_typecastt::c_typet c_typecastt::get_c_type(
  const typet &type)
{
  unsigned width=type.get_int(ID_width);

  if(type.id()==ID_signedbv)
  {
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
  else if(type.id()==ID_floatbv ||
          type.id()==ID_fixedbv)
  {
    if(width<=config.ansi_c.single_width)
      return SINGLE;
    else if(width<=config.ansi_c.double_width)
      return DOUBLE;
    else if(width<=config.ansi_c.long_double_width)
      return LONGDOUBLE;
    else if(width<=128)
      return FLOAT128;
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
  else if(type.id()==ID_c_enum ||
          type.id()==ID_c_enum_tag ||
          type.id()==ID_incomplete_c_enum)
  {
    return INT;
  }
  else if(type.id()==ID_symbol)
    return get_c_type(ns.follow(type));
  else if(type.id()==ID_rational)
    return RATIONAL;
  else if(type.id()==ID_real)
    return REAL;
  else if(type.id()==ID_complex)
    return COMPLEX;
  else if(type.id()==ID_c_bit_field)
    return get_c_type(to_c_bit_field_type(type).subtype());
    
  return OTHER;  
}

/*******************************************************************\

Function: c_typecastt::implicit_typecast_arithmetic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecastt::implicit_typecast_arithmetic(
  exprt &expr,
  c_typet c_type)
{
  typet new_type;
  
  const typet &expr_type=ns.follow(expr.type());
  
  switch(c_type)
  {
  case PTR:
    if(expr_type.id()==ID_array)
    {
      new_type.id(ID_pointer);
      new_type.subtype()=expr_type.subtype();
      break;
    }
    return;

  case BOOL:       assert(false); // should always be promoted to int
  case CHAR:       assert(false); // should always be promoted to int
  case UCHAR:      assert(false); // should always be promoted to int
  case SHORT:      assert(false); // should always be promoted to int
  case USHORT:     assert(false); // should always be promoted to int
  case INT:        new_type=signed_int_type(); break;
  case UINT:       new_type=unsigned_int_type(); break;
  case LONG:       new_type=signed_long_int_type(); break;
  case ULONG:      new_type=unsigned_long_int_type(); break;
  case LONGLONG:   new_type=signed_long_long_int_type(); break;
  case ULONGLONG:  new_type=unsigned_long_long_int_type(); break;
  case SINGLE:     new_type=float_type(); break;
  case DOUBLE:     new_type=double_type(); break;
  case LONGDOUBLE: new_type=long_double_type(); break;
  case FLOAT128:   new_type=ieee_float_spect::quadruple_precision().to_type(); break;
  case RATIONAL:   new_type=rational_typet(); break;
  case REAL:       new_type=real_typet(); break;
  case INTEGER:    new_type=integer_typet(); break;
  case COMPLEX: return; // do nothing
  default: return;
  }

  if(new_type!=expr_type)
    do_typecast(expr, new_type);
}

/*******************************************************************\

Function: c_typecastt::implicit_typecast_arithmetic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecastt::implicit_typecast_arithmetic(exprt &expr)
{
  c_typet c_type=get_c_type(expr.type());
  c_type=std::max(c_type, INT); // minimum promotion
  implicit_typecast_arithmetic(expr, c_type);
}

/*******************************************************************\

Function: c_typecastt::implicit_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: c_typecastt::implicit_typecast_followed

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    const union_typet &dest_union_type=to_union_type(dest_type);

    for(union_typet::componentst::const_iterator
        it=dest_union_type.components().begin();
        it!=dest_union_type.components().end();
        it++)
    {
      if(!check_c_implicit_typecast(src_type_no_const, it->type()))
      {
        // build union constructor
        exprt union_expr(ID_union, orig_dest_type);
        union_expr.move_to_operands(expr);
        if(!full_eq(src_type, src_type_no_const))
          do_typecast(union_expr.op0(), src_type_no_const);
        union_expr.set(ID_component_name, it->get_name());
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
      
      const typet &src_sub=ns.follow(src_type.subtype());
      const typet &dest_sub=ns.follow(dest_type.subtype());

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
      else if((is_number(src_sub) || src_sub.id()==ID_c_enum || src_sub.id()==ID_c_enum_tag) &&
              (is_number(dest_sub) || dest_sub.id()==ID_c_enum || src_sub.id()==ID_c_enum_tag))
      {
        // Also generous: between any to scalar types it's ok.
        // We should probably check the size.
      }
      else
        warnings.push_back("incompatible pointer types");

      // check qualifiers

      /*
      if(src_type.subtype().get_bool(ID_C_constant) &&
         !dest_type.subtype().get_bool(ID_C_constant))
        warnings.push_back("disregarding const");
      */

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

/*******************************************************************\

Function: c_typecastt::implicit_typecast_arithmetic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecastt::implicit_typecast_arithmetic(
  exprt &expr1,
  exprt &expr2)
{
  const typet &type1=ns.follow(expr1.type());
  const typet &type2=ns.follow(expr2.type());

  c_typet c_type1=get_c_type(type1),
          c_type2=get_c_type(type2);

  c_typet max_type=std::max(c_type1, c_type2);

  // "If an int can represent all values of the original type, the
  // value is converted to an int; otherwise, it is converted to
  // an unsigned int."
  
  // The second case can arise if we promote any unsigned type
  // that is as large as unsigned int.

  if(config.ansi_c.short_int_width==config.ansi_c.int_width &&
     max_type==USHORT)
    max_type=UINT;
  else if(config.ansi_c.char_width==config.ansi_c.int_width &&
          max_type==UCHAR)
    max_type=UINT;
  else
    max_type=std::max(max_type, INT);

  if(max_type==LARGE_SIGNED_INT || max_type==LARGE_UNSIGNED_INT)
  {
    // get the biggest width of both
    unsigned width1=type1.get_int(ID_width);
    unsigned width2=type2.get_int(ID_width);
    
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

  if(max_type==PTR)
  {
    if(c_type1==VOIDPTR)
      do_typecast(expr1, expr2.type());
    
    if(c_type2==VOIDPTR)
      do_typecast(expr2, expr1.type());
  }
}

/*******************************************************************\

Function: c_typecastt::do_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecastt::do_typecast(exprt &expr, const typet &dest_type)
{
  // special case: array -> pointer is actually
  // something like address_of
  
  const typet &src_type=ns.follow(expr.type());

  if(src_type.id()==ID_array)
  {
    index_exprt index;
    index.array()=expr;
    index.index()=gen_zero(index_type());
    index.type()=src_type.subtype();
    expr=address_of_exprt(index);
    if(ns.follow(expr.type())!=ns.follow(dest_type))
      expr.make_typecast(dest_type);
    return;
  }

  if(src_type!=dest_type)
  {
    // C booleans are special; we produce the
    // explicit comparision with zero.
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
