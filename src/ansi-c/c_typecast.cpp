/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <cstdlib>

#include <config.h>
#include <expr_util.h>
#include <std_expr.h>
#include <base_type.h>
#include <symbol.h>

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

  if(src_type_id==ID_natural)
  {
    if(dest_type.id()==ID_bool) return false;
    if(dest_type.id()==ID_integer) return false;
    if(dest_type.id()==ID_real) return false;
    if(dest_type.id()==ID_complex) return false;
    if(dest_type.id()==ID_unsignedbv) return false;
    if(dest_type.id()==ID_signedbv) return false;
    if(dest_type.id()==ID_floatbv) return false;
  }
  else if(src_type_id==ID_integer)
  {
    if(dest_type.id()==ID_bool) return false;
    if(dest_type.id()==ID_real) return false;
    if(dest_type.id()==ID_complex) return false;
    if(dest_type.id()==ID_unsignedbv) return false;
    if(dest_type.id()==ID_signedbv) return false;
    if(dest_type.id()==ID_floatbv) return false;
    if(dest_type.id()==ID_fixedbv) return false;
    if(dest_type.id()==ID_pointer) return false;
  }
  else if(src_type_id==ID_real)
  {
    if(dest_type.id()==ID_bool) return false;
    if(dest_type.id()==ID_complex) return false;
    if(dest_type.id()==ID_floatbv) return false;
    if(dest_type.id()==ID_fixedbv) return false;
  }
  else if(src_type_id==ID_rational)
  {
    if(dest_type.id()==ID_bool) return false;
    if(dest_type.id()==ID_complex) return false;
    if(dest_type.id()==ID_floatbv) return false;
    if(dest_type.id()==ID_fixedbv) return false;
  }
  else if(src_type_id==ID_bool)
  {
    if(dest_type.id()==ID_integer) return false;
    if(dest_type.id()==ID_real) return false;
    if(dest_type.id()==ID_unsignedbv) return false;
    if(dest_type.id()==ID_signedbv) return false;
    if(dest_type.id()==ID_pointer) return false;
    if(dest_type.id()==ID_floatbv) return false;
    if(dest_type.id()==ID_fixedbv) return false;
    if(dest_type.id()==ID_c_enum) return false;
  }
  else if(src_type_id==ID_unsignedbv ||
          src_type_id==ID_signedbv ||
          src_type_id==ID_c_enum ||
          src_type_id==ID_incomplete_c_enum)
  {
    if(dest_type.id()==ID_unsignedbv) return false;
    if(dest_type.id()==ID_bool) return false;
    if(dest_type.id()==ID_integer) return false;
    if(dest_type.id()==ID_real) return false;
    if(dest_type.id()==ID_rational) return false;
    if(dest_type.id()==ID_signedbv) return false;
    if(dest_type.id()==ID_floatbv) return false;
    if(dest_type.id()==ID_fixedbv) return false;
    if(dest_type.id()==ID_pointer) return false;
    if(dest_type.id()==ID_c_enum) return false;
    if(dest_type.id()==ID_incomplete_c_enum) return false;
  }
  else if(src_type_id==ID_floatbv ||
          src_type_id==ID_fixedbv)
  {
    if(dest_type.id()==ID_bool) return false;
    if(dest_type.id()==ID_integer) return false;
    if(dest_type.id()==ID_real) return false;
    if(dest_type.id()==ID_rational) return false;
    if(dest_type.id()==ID_signedbv) return false;
    if(dest_type.id()==ID_unsignedbv) return false;
    if(dest_type.id()==ID_floatbv) return false;
    if(dest_type.id()==ID_fixedbv) return false;
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
    if(dest_type.id()==ID_unsignedbv) return false;
    if(dest_type.id()==ID_signedbv) return false;
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

  typet dest_type=src_type;
  
  // collect qualifiers
  c_qualifierst qualifiers;
  
  // hack for something that isn't a proper type qualifier
  bool transparent_union=false;
  
  while(dest_type.id()==ID_symbol)
  {
    qualifiers+=c_qualifierst(dest_type);

    if(dest_type.get_bool(ID_transparent_union))
      transparent_union=true;
  
    const symbolt &followed_type_symbol=
      ns.lookup(dest_type.get(ID_identifier));

    dest_type=followed_type_symbol.type;
  }

  qualifiers.write(dest_type);

  if(transparent_union)
    dest_type.set(ID_transparent_union, true);
  
  return dest_type;
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
  unsigned width=atoi(type.get(ID_width).c_str());
  
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
  }
  else if(type.id()==ID_bool)
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

  case BOOL:       new_type=bool_typet(); break;
  case CHAR:       assert(false); // should always be promoted to int
  case UCHAR:      assert(false); // should always be promoted to int
  case SHORT:      assert(false); // should always be promoted to int
  case USHORT:     assert(false); // should always be promoted to int
  case INT:        new_type=int_type(); break;
  case UINT:       new_type=uint_type(); break;
  case LONG:       new_type=long_int_type(); break;
  case ULONG:      new_type=long_uint_type(); break;
  case LONGLONG:   new_type=long_long_int_type(); break;
  case ULONGLONG:  new_type=long_long_uint_type(); break;
  case SINGLE:     new_type=float_type(); break;
  case DOUBLE:     new_type=double_type(); break;
  case LONGDOUBLE: new_type=long_double_type(); break;
  case RATIONAL:   new_type=rational_typet(); break;
  case REAL:       new_type=real_typet(); break;
  case INTEGER:    new_type=integer_typet(); break;
  default: return;
  }

  if(new_type!=expr_type)
  {
    if(new_type.id()==ID_pointer &&
       expr_type.id()==ID_array)
    {
      exprt index_expr(ID_index, expr_type.subtype());
      index_expr.reserve_operands(2);
      index_expr.move_to_operands(expr);
      index_expr.copy_to_operands(gen_zero(index_type()));
      expr=exprt(ID_address_of, new_type);
      expr.move_to_operands(index_expr);
    }
    else
      do_typecast(expr, new_type);
  }
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
  
  implicit_typecast_followed(expr, src_type, dest_type);
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
  const typet &dest_type)
{
  // do transparent union
  if(dest_type.id()==ID_union &&
     dest_type.get_bool(ID_transparent_union) &&
     src_type.id()!=ID_union)
  {
    // check union members
    const union_typet &union_type=to_union_type(dest_type);

    for(union_typet::componentst::const_iterator
        it=union_type.components().begin();
        it!=union_type.components().end();
        it++)
    {
      if(!check_c_implicit_typecast(src_type, it->type()))
      {
        // build union constructor
        exprt union_expr(ID_union, union_type);
        union_expr.move_to_operands(expr);
        union_expr.set(ID_component_name, it->get_name());
        expr=union_expr;
        return; // ok
      }
    }
  }

  if(dest_type.id()==ID_pointer)
  {
    // special case: 0 == NULL

    if(expr.is_zero() && (
       src_type.id()==ID_unsignedbv ||
       src_type.id()==ID_signedbv ||
       src_type.id()==ID_natural ||
       src_type.id()==ID_integer))
    {
      expr=exprt(ID_constant, dest_type);
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
      else if(base_type_eq(src_type.subtype(), dest_type.subtype(), ns))
      {
        // ok
      }
      else if(is_number(src_sub) && is_number(dest_sub))
      {
        // also generous: between any to scalar types it's ok
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
        do_typecast(expr, dest_type);

      return; // ok
    }
  }
  
  if(check_c_implicit_typecast(src_type, dest_type))
    errors.push_back("implicit conversion not permitted");
  else if(src_type!=dest_type)
    do_typecast(expr, dest_type);
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

void c_typecastt::do_typecast(exprt &dest, const typet &type)
{
  // special case: array -> pointer is actually
  // something like address_of
  
  const typet &dest_type=ns.follow(dest.type());

  if(dest_type.id()==ID_array)
  {
    index_exprt index;
    index.array()=dest;
    index.index()=gen_zero(index_type());
    index.type()=dest_type.subtype();
    dest=address_of_exprt(index);
    if(ns.follow(dest.type())!=ns.follow(type))
      dest.make_typecast(type);
    return;
  }

  if(dest_type!=type)
    dest.make_typecast(type);
}
