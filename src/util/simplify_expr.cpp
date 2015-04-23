/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <algorithm>

#include "simplify_expr_class.h"
#include "simplify_expr.h"
#include "mp_arith.h"
#include "arith_tools.h"
#include "replace_expr.h"
#include "std_types.h"
#include "bitvector.h"
#include "simplify_utils.h"
#include "expr_util.h"
#include "std_expr.h"
#include "fixedbv.h"
#include "ieee_float.h"
#include "pointer_offset_size.h"
#include "rational.h"
#include "rational_tools.h"
#include "config.h"
#include "base_type.h"
#include "namespace.h"
#include "threeval.h"
#include "pointer_predicates.h"
#include "prefix.h"
#include "byte_operators.h"

//#define DEBUGX

#ifdef DEBUGX
#include <langapi/language_util.h>
#include <iostream>
#endif

//#define USE_CACHE

#ifdef USE_CACHE
struct simplify_expr_cachet
{
public:
  friend class simplify_exprt;

  #if 1
  typedef hash_map_cont<
    exprt, exprt, irep_full_hash, irep_full_eq> containert;
  #else
  typedef hash_map_cont<
    exprt, exprt, irep_hash> containert;
  #endif
    
  containert container_normal;
  
  containert &container()
  {
    return container_normal;
  }
};

simplify_expr_cachet simplify_expr_cache;
#endif

/*******************************************************************\

Function: simplify_exprt::setup_jump_table

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

// ugly global object

std::vector<simplify_exprt::jump_table_entryt> simplify_jump_table;

#define ENTRY(id, member) \
  if(simplify_jump_table.size()<=(id).get_no()) \
    simplify_jump_table.resize((id).get_no()+1, 0); \
  simplify_jump_table[(id).get_no()]=&simplify_exprt::member;

void simplify_exprt::setup_jump_table()
{
  // done already?
  if(!simplify_jump_table.empty()) return;

  ENTRY(ID_typecast, simplify_typecast);
  ENTRY(ID_extractbit, simplify_extractbit);
  ENTRY(ID_extractbits, simplify_extractbits);
  ENTRY(ID_concatenation, simplify_concatenation);
  ENTRY(ID_mult, simplify_mult);
  ENTRY(ID_div, simplify_div);
  ENTRY(ID_mod, simplify_mod);
  ENTRY(ID_plus, simplify_plus);
  ENTRY(ID_minus, simplify_minus);
  ENTRY(ID_floatbv_plus, simplify_floatbv_op);
  ENTRY(ID_floatbv_minus, simplify_floatbv_op);
  ENTRY(ID_floatbv_mult, simplify_floatbv_op);
  ENTRY(ID_floatbv_div, simplify_floatbv_op);
  ENTRY(ID_floatbv_typecast, simplify_floatbv_typecast);
  ENTRY(ID_ashr, simplify_shifts);
  ENTRY(ID_lshr, simplify_shifts);
  ENTRY(ID_shl, simplify_shifts);
  ENTRY(ID_bitnot, simplify_bitwise);
  ENTRY(ID_bitand, simplify_bitwise);
  ENTRY(ID_bitor, simplify_bitwise);
  ENTRY(ID_bitxor, simplify_bitwise);
  ENTRY(ID_if, simplify_if);
  ENTRY(ID_bitnot, simplify_bitnot);
  ENTRY(ID_not, simplify_not);
  ENTRY(ID_implies, simplify_boolean);
  ENTRY(ID_iff, simplify_boolean);
  ENTRY(ID_or, simplify_boolean);
  ENTRY(ID_xor, simplify_boolean);
  ENTRY(ID_and, simplify_boolean);
  ENTRY(ID_equal, simplify_inequality);
  ENTRY(ID_notequal, simplify_inequality);
  ENTRY(ID_gt, simplify_inequality);
  ENTRY(ID_lt, simplify_inequality);
  ENTRY(ID_ge, simplify_inequality);
  ENTRY(ID_le, simplify_inequality);
  ENTRY(ID_ieee_float_equal, simplify_ieee_float_relation);
  ENTRY(ID_ieee_float_notequal, simplify_ieee_float_relation);
  ENTRY(ID_lambda, simplify_lambda);
  ENTRY(ID_with, simplify_with);
  ENTRY(ID_update, simplify_update);
  ENTRY(ID_index, simplify_index);
  ENTRY(ID_member, simplify_member);
  ENTRY(ID_byte_update_little_endian, simplify_byte_update);
  ENTRY(ID_byte_update_big_endian, simplify_byte_update);
  ENTRY(ID_byte_extract_little_endian, simplify_byte_extract);
  ENTRY(ID_byte_extract_big_endian, simplify_byte_extract);
  ENTRY(ID_pointer_object, simplify_pointer_object);
  ENTRY(ID_object_size, simplify_object_size);
  ENTRY(ID_dynamic_object, simplify_dynamic_object);
  ENTRY(ID_invalid_pointer, simplify_invalid_pointer);
  ENTRY(ID_good_pointer, simplify_good_pointer);
  ENTRY(ID_unary_minus, simplify_unary_minus);
  ENTRY(ID_unary_plus, simplify_unary_plus);
  ENTRY(ID_dereference, simplify_dereference);
  ENTRY(ID_address_of, simplify_address_of);
  ENTRY(ID_pointer_offset, simplify_pointer_offset);
  ENTRY(ID_isinf, simplify_isinf);
  ENTRY(ID_isnan, simplify_isnan);
  ENTRY(ID_isnormal, simplify_isnormal);
  ENTRY(ID_abs, simplify_abs);
  ENTRY(ID_sign, simplify_sign);
}

/*******************************************************************\

Function: simplify_exprt::simplify_isinf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_isinf(exprt &expr)
{
  if(expr.operands().size()!=1) return true;

  if(ns.follow(expr.op0().type()).id()!=ID_floatbv)
    return true;
 
  if(expr.op0().is_constant())
  {
    ieee_floatt value(to_constant_expr(expr.op0()));
    expr.make_bool(value.is_infinity());
    return false;
  }
  
  return true; 
}

/*******************************************************************\

Function: simplify_exprt::simplify_isnan

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_isnan(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
 
  if(expr.op0().is_constant())
  {
    ieee_floatt value(to_constant_expr(expr.op0()));
    expr.make_bool(value.is_NaN());
    return false;
  }
  
  return true; 
}

/*******************************************************************\

Function: simplify_exprt::simplify_isnormal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_isnormal(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
 
  if(expr.op0().is_constant())
  {
    ieee_floatt value(to_constant_expr(expr.op0()));
    expr.make_bool(value.is_normal());
    return false;
  }
  
  return true; 
}

/*******************************************************************\

Function: simplify_exprt::simplify_abs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_abs(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
 
  if(expr.op0().is_constant())
  {
    const typet &type=ns.follow(expr.op0().type());
    
    if(type.id()==ID_floatbv)
    {
      ieee_floatt value(to_constant_expr(expr.op0()));
      value.set_sign(false);
      expr=value.to_expr();
      return false;
    }
    else if(type.id()==ID_signedbv ||
            type.id()==ID_unsignedbv)
    {
      mp_integer value;
      if(!to_integer(expr.op0(), value))
      {
        if(value>=0)
        {
          expr=expr.op0();
          return false;
        }
        else
        {
          value.negate();
          expr=from_integer(value, type);
          return false;
        }
      }
    }
  }
  
  return true; 
}

/*******************************************************************\

Function: simplify_exprt::simplify_sign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_sign(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
 
  if(expr.op0().is_constant())
  {
    const typet &type=ns.follow(expr.op0().type());
    
    if(type.id()==ID_floatbv)
    {
      ieee_floatt value(to_constant_expr(expr.op0()));
      expr.make_bool(value.get_sign());
      return false;
    }
    else if(type.id()==ID_signedbv ||
            type.id()==ID_unsignedbv)
    {
      mp_integer value;
      if(!to_integer(expr.op0(), value))
      {
        expr.make_bool(value>=0);
        return false;
      }
    }
  }
  
  return true; 
}

/*******************************************************************\

Function: simplify_exprt::simplify_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_typecast(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
  
  const typet &expr_type=ns.follow(expr.type());
  const typet &op_type=ns.follow(expr.op0().type());

  // eliminate casts of infinity
  if(expr.op0().id()==ID_infinity)
  {
    typet new_type=expr.type();
    exprt tmp;
    tmp.swap(expr.op0());
    tmp.type()=new_type;
    expr.swap(tmp);
    return false;
  }
  
  // casts from NULL to any integer
  if(op_type.id()==ID_pointer &&
     expr.op0().is_constant() &&
     to_constant_expr(expr.op0()).get_value()==ID_NULL &&
     (expr_type.id()==ID_unsignedbv || expr_type.id()==ID_signedbv) &&
     config.ansi_c.NULL_is_zero)
  {
    exprt tmp=gen_zero(expr_type);
    expr.swap(tmp);
    return false;
  }
  
  // casts from pointer to integer
  // where width of integer >= width of pointer
  // (void*)(intX)expr -> (void*)expr
  if(expr_type.id()==ID_pointer &&
     expr.op0().id()==ID_typecast &&
     expr.op0().operands().size()==1 &&
     (op_type.id()==ID_signedbv || op_type.id()==ID_unsignedbv) &&
     to_bitvector_type(op_type).get_width() >= config.ansi_c.pointer_width)
  {
    exprt tmp=expr.op0().op0();
    expr.op0().swap(tmp);
    simplify_typecast(expr); // rec. call
    return false;
  }

  // eliminate redundant typecasts
  if(base_type_eq(expr.type(), expr.op0().type(), ns))
  {
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
    return false;
  }

  // elminiate casts to proper bool
  if(expr_type.id()==ID_bool)
  {
    // rewrite (bool)x to x!=0
    binary_relation_exprt inequality;
    inequality.id(op_type.id()==ID_floatbv?ID_ieee_float_notequal:ID_notequal);
    inequality.add_source_location()=expr.source_location();
    inequality.lhs()=expr.op0();
    inequality.rhs()=gen_zero(ns.follow(expr.op0().type()));
    assert(inequality.rhs().is_not_nil());
    simplify_node(inequality);
    expr.swap(inequality);
    return false;
  }
  
  // elminiate casts to _Bool
  if(expr_type.id()==ID_c_bool &&
     op_type.id()!=ID_bool)
  {
    // rewrite (_Bool)x to (_Bool)(x!=0)
    binary_relation_exprt inequality;
    inequality.id(op_type.id()==ID_floatbv?ID_ieee_float_notequal:ID_notequal);
    inequality.add_source_location()=expr.source_location();
    inequality.lhs()=expr.op0();
    inequality.rhs()=gen_zero(ns.follow(expr.op0().type()));
    assert(inequality.rhs().is_not_nil());
    simplify_node(inequality);
    expr.op0()=inequality;
    simplify_typecast(expr); // recursive call
    return false;
  }
  
  // eliminate typecasts from NULL
  if(expr_type.id()==ID_pointer &&
     expr.op0().is_constant() &&
     to_constant_expr(expr.op0()).get_value()==ID_NULL)
  {
    exprt tmp=expr.op0();
    tmp.type()=expr.type();
    expr.swap(tmp);
    return false;
  }

  // eliminate duplicate pointer typecasts
  // (T1 *)(T2 *)x -> (T1 *)x
  if(expr_type.id()==ID_pointer &&
     expr.op0().id()==ID_typecast &&
     op_type.id()==ID_pointer &&
     expr.op0().operands().size()==1)
  {
    exprt tmp;
    tmp.swap(expr.op0().op0());
    expr.op0().swap(tmp);
    // recursive call
    simplify_node(expr);
    return false;
  }
  
  // casts from integer to pointer and back:
  // (int)(void *)int -> (int)(size_t)int
  if((expr_type.id()==ID_signedbv || expr_type.id()==ID_unsignedbv) &&
     expr.op0().id()==ID_typecast &&
     expr.op0().operands().size()==1 &&
     op_type.id()==ID_pointer)
  {
    expr.op0().type()=unsignedbv_typet(config.ansi_c.pointer_width);
    simplify_typecast(expr.op0()); // rec. call
    simplify_typecast(expr); // rec. call
    return false;
  }
  
  // Push a numerical typecast into various integer operations, i.e.,
  // (T)(x OP y) ---> (T)x OP (T)y
  //
  // Doesn't work for many, e.g., pointer difference, floating-point,
  // division, modulo.
  // Many operations fail if the width of T
  // is bigger than that of (x OP y). This includes ID_bitnot and
  // anything that might overflow, e.g., ID_plus.
  //
  if((expr_type.id()==ID_signedbv || expr_type.id()==ID_unsignedbv) &&
     (op_type.id()==ID_signedbv || op_type.id()==ID_unsignedbv))
  {
    bool enlarge=
      to_bitvector_type(expr_type).get_width() > to_bitvector_type(op_type).get_width();

    if(!enlarge)
    {
      irep_idt op_id=expr.op0().id();
    
      if(op_id==ID_plus || op_id==ID_minus || op_id==ID_mult ||
         op_id==ID_unary_minus || 
         op_id==ID_bitxor || op_id==ID_bitor || op_id==ID_bitand)
      {
        exprt result=expr.op0();
        
        if(result.operands().size()>=1 && 
           base_type_eq(result.op0().type(), result.type(), ns))
        {
          result.type()=expr.type();

          Forall_operands(it, result)
          {
            it->make_typecast(expr.type());
            simplify_typecast(*it); // recursive call
          }

          simplify_node(result); // possibly recursive call
          expr.swap(result);
          return false;
        }
      }
      else if(op_id==ID_ashr || op_id==ID_lshr || op_id==ID_shl)
      {
      }
    }
  }

  #if 0
  // (T)(a?b:c) --> a?(T)b:(T)c
  if(expr.op0().id()==ID_if &&
     expr.op0().operands().size()==3)
  {
    exprt tmp_op1=typecast_exprt(expr.op0().op1(), expr_type);
    exprt tmp_op2=typecast_exprt(expr.op0().op2(), expr_type);
    simplify_typecast(tmp_op1);
    simplify_typecast(tmp_op2);
    expr=if_exprt(expr.op0().op0(), tmp_op1, tmp_op2, expr_type);
    simplify_if(expr);
    return false;
  }
  #endif
  
  const irep_idt &expr_type_id=expr_type.id();
  const exprt &operand=expr.op0();
  const irep_idt &op_type_id=op_type.id();

  unsigned expr_width=bv_width(expr_type);
  unsigned op_width=bv_width(operand.type());
  
  if(operand.is_constant())
  {
    const irep_idt &value=to_constant_expr(operand).get_value();
    
    // preserve the sizeof type annotation
    typet c_sizeof_type=
      static_cast<const typet &>(operand.find(ID_C_c_sizeof_type));
      
    if(op_type_id==ID_integer ||
       op_type_id==ID_natural)
    {
      // from integer to ...
    
      mp_integer int_value=string2integer(id2string(value));

      if(expr_type_id==ID_bool)
      {
        expr.make_bool(int_value!=0);
        return false;
      }

      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv ||
         expr_type_id==ID_c_enum ||
         expr_type_id==ID_c_bit_field ||
         expr_type_id==ID_integer)
      {
        expr=from_integer(int_value, expr_type);
        return false;
      }
    }
    else if(op_type_id==ID_rational)
    {
    }
    else if(op_type_id==ID_real)
    {
    }
    else if(op_type_id==ID_bool)
    {
      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv ||
         expr_type_id==ID_integer ||
         expr_type_id==ID_natural ||
         expr_type_id==ID_rational ||
         expr_type_id==ID_c_bool ||
         expr_type_id==ID_c_enum ||
         expr_type_id==ID_c_bit_field)
      {
        if(operand.is_true())
        {
          expr=gen_one(expr_type);
          assert(expr.is_not_nil());
          return false;
        }
        else if(operand.is_false())
        {
          expr=gen_zero(expr_type);
          assert(expr.is_not_nil());
          return false;
        }
      }
      else if(expr_type_id==ID_c_enum_tag)
      {
        const typet &c_enum_type=ns.follow_tag(to_c_enum_tag_type(expr_type));
        if(c_enum_type.id()==ID_c_enum) // possibly incomplete
        {
          unsigned int_value=operand.is_true();
          exprt tmp=from_integer(int_value, c_enum_type);
          tmp.type()=expr_type; // we maintain the tag type
          expr=tmp;
          return false;
        }
      }
    }
    else if(op_type_id==ID_unsignedbv ||
            op_type_id==ID_signedbv ||
            op_type_id==ID_c_bit_field ||
            op_type_id==ID_c_bool)
    {
      mp_integer int_value;
      
      if(to_integer(to_constant_expr(operand), int_value))
        return true;

      if(expr_type_id==ID_bool)
      {
        expr.make_bool(int_value!=0);
        return false;
      }

      if(expr_type_id==ID_c_bool)
      {
        expr=from_integer(int_value!=0, expr_type);
        return false;
      }
      
      if(expr_type_id==ID_integer)
      {
        expr=from_integer(int_value, expr_type);
        return false;
      }

      if(expr_type_id==ID_natural)
      {
        if(int_value>=0)
        {
          expr=from_integer(int_value, expr_type);
          return false;
        }
      }

      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv ||
         expr_type_id==ID_bv ||
         expr_type_id==ID_c_bit_field)
      {
        expr=from_integer(int_value, expr_type);

        if(c_sizeof_type.is_not_nil())
          expr.set(ID_C_c_sizeof_type, c_sizeof_type);

        return false;
      }
      
      if(expr_type_id==ID_c_enum_tag)
      {
        const typet &c_enum_type=ns.follow_tag(to_c_enum_tag_type(expr_type));
        if(c_enum_type.id()==ID_c_enum) // possibly incomplete
        {
          exprt tmp=from_integer(int_value, c_enum_type);
          tmp.type()=expr_type; // we maintain the tag type
          expr=tmp;
          return false;
        }
      }
      
      if(expr_type_id==ID_c_enum)
      {
        expr=from_integer(int_value, expr_type);
        return false;
      }
      
      if(expr_type_id==ID_fixedbv)
      {
        // int to float
        const fixedbv_typet &f_expr_type=
          to_fixedbv_type(expr_type);

        fixedbvt f;
        f.spec=f_expr_type;
        f.from_integer(int_value);
        expr=f.to_expr();

        return false;
      }

      if(expr_type_id==ID_floatbv)
      {
        // int to float
        const floatbv_typet &f_expr_type=
          to_floatbv_type(expr_type);

        ieee_floatt f;
        f.spec=f_expr_type;
        f.from_integer(int_value);
        expr=f.to_expr();

        return false;
      }

      if(expr_type_id==ID_rational)
      {
        rationalt r=int_value;
        expr=from_rational(r);
        return false;
      }

    }
    else if(op_type_id==ID_fixedbv)
    {
      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv)
      {
        // cast from float to int
        fixedbvt f(to_constant_expr(expr.op0()));
        expr=from_integer(f.to_integer(), expr_type);
        return false;
      }
      else if(expr_type_id==ID_fixedbv)
      {
        // float to double or double to float
        fixedbvt f(to_constant_expr(expr.op0()));
        f.round(to_fixedbv_type(expr_type));
        expr=f.to_expr();
        return false;
      }
    }
    else if(op_type_id==ID_floatbv)
    {
      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv)
      {
        // cast from float to int
        ieee_floatt f(to_constant_expr(expr.op0()));
        expr=from_integer(f.to_integer(), expr_type);
        return false;
      }
      else if(expr_type_id==ID_floatbv)
      {
        // float to double or double to float
        ieee_floatt f(to_constant_expr(expr.op0()));
        f.change_spec(to_floatbv_type(expr_type));
        expr=f.to_expr();
        return false;
      }
    }
    else if(op_type_id==ID_bv)
    {
      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv ||
         expr_type_id==ID_floatbv)
      {
        mp_integer int_value=binary2integer(id2string(value), false);
        expr=from_integer(int_value, expr_type);
        return false;
      }
    }
    else if(op_type_id==ID_c_enum_tag) // enum to int
    {
      const typet &base_type=ns.follow_tag(to_c_enum_tag_type(op_type)).subtype();
      if(base_type.id()==ID_signedbv || base_type.id()==ID_unsignedbv)
      {
        // enum constants use the representation of their base type
        expr.op0().type()=base_type;
        simplify_typecast(expr);
        return false;
      }
    }
    else if(op_type_id==ID_c_enum) // enum to int
    {
      const typet &base_type=to_c_enum_type(op_type).subtype();
      if(base_type.id()==ID_signedbv || base_type.id()==ID_unsignedbv)
      {
        // enum constants use the representation of their base type
        expr.op0().type()=base_type;
        simplify_typecast(expr);
        return false;
      }
    }
  }
  else if(operand.id()==ID_typecast) // typecast of typecast
  {
    // (T1)(T2)x ---> (T1)
    // where T1 has fewer bits than T2
    if(operand.operands().size()==1 &&
       op_type_id==expr_type_id &&
       (expr_type_id==ID_unsignedbv || expr_type_id==ID_signedbv) &&
       expr_width<=op_width)
    {
      exprt tmp;
      tmp.swap(expr.op0().op0());
      expr.op0().swap(tmp);
      // might enable further simplification
      simplify_typecast(expr); // recursive call
      return false;
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_dereference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_dereference(exprt &expr)
{
  const exprt &pointer=to_dereference_expr(expr).pointer();

  if(pointer.type().id()!=ID_pointer) return true;
  
  if(pointer.id()==ID_address_of)
  {
    exprt tmp=to_address_of_expr(pointer).object();
    // one address_of is gone, try again
    simplify_rec(tmp);
    expr.swap(tmp);
    return false;
  }
  // rewrite *(&a[0] + x) to a[x]
  else if(pointer.id()==ID_plus &&
          pointer.operands().size()==2 &&
          pointer.op0().id()==ID_address_of)
  {
    const address_of_exprt &address_of=
      to_address_of_expr(pointer.op0());
    if(address_of.object().id()==ID_index)
    {
      const index_exprt &old=to_index_expr(address_of.object());
      if(ns.follow(old.array().type()).id()==ID_array)
      {
        index_exprt idx(old.array(),
                        plus_exprt(old.index(), pointer.op1()),
                        ns.follow(old.array().type()).subtype());
        simplify_rec(idx);
        expr.swap(idx);
        return false;
      }
    }
  }

  return true;
}

/*******************************************************************\

Function: is_dereference_integer_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static bool is_dereference_integer_object(
  const exprt &expr,
  mp_integer &address)
{
  if(expr.id()==ID_dereference &&
     expr.operands().size()==1)
  {
    if(expr.op0().id()==ID_typecast &&
       expr.op0().operands().size()==1 &&
       expr.op0().op0().is_constant() &&
       !to_integer(expr.op0().op0(), address))
      return true;

    if(expr.op0().is_constant())
    {
      if(to_constant_expr(expr.op0()).get_value()==ID_NULL &&
         config.ansi_c.NULL_is_zero) // NULL
      {
        address=0;
        return true;
      }
      else if(!to_integer(expr.op0(), address))
        return true;
    }
  }
  
  return false;
}

/*******************************************************************\

Function: simplify_exprt::simplify_address_of_arg

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_address_of_arg(exprt &expr)
{
  if(expr.id()==ID_index)
  {
    if(expr.operands().size()==2)
    {
      bool result=true;
      if(!simplify_address_of_arg(expr.op0())) result=false;
      if(!simplify_rec(expr.op1())) result=false;

      // rewrite (*(type *)int) [index] by
      // pushing the index inside
      
      mp_integer address;
      if(is_dereference_integer_object(expr.op0(), address))
      {
        // push index into address
        
        mp_integer step_size, index;
        
        step_size=pointer_offset_size(expr.type(), ns);
        
        if(!to_integer(expr.op1(), index) &&
           step_size!=-1)
        {
          unsignedbv_typet int_type(config.ansi_c.pointer_width);
          pointer_typet pointer_type;
          pointer_type.subtype()=expr.type();
          typecast_exprt typecast_expr(
            from_integer(step_size*index+address, int_type), pointer_type);
          exprt new_expr=dereference_exprt(typecast_expr, expr.type());
          expr=new_expr;
          result=true;
        }
      }

      return result;
    }
  }
  else if(expr.id()==ID_member)
  {
    if(expr.operands().size()==1)
    {
      bool result=true;
      if(!simplify_address_of_arg(expr.op0())) result=false;

      const typet &op_type=ns.follow(expr.op0().type());

      if(op_type.id()==ID_struct)
      {
        // rewrite NULL -> member by
        // pushing the member inside

        mp_integer address;
        if(is_dereference_integer_object(expr.op0(), address))
        {
          const struct_typet &struct_type=to_struct_type(op_type);
          const irep_idt &member=to_member_expr(expr).get_component_name();
          mp_integer offset=member_offset(struct_type, member, ns);
          if(offset!=-1)
          {
            unsignedbv_typet int_type(config.ansi_c.pointer_width);
            pointer_typet pointer_type;
            pointer_type.subtype()=expr.type();
            typecast_exprt typecast_expr(
              from_integer(address+offset, int_type), pointer_type);
            exprt new_expr=dereference_exprt(typecast_expr, expr.type());
            expr=new_expr;
            result=true;
          }          
        }
      }
      
      return result;
    }
  }
  else if(expr.id()==ID_dereference)
  {
    if(expr.operands().size()==1)
      return simplify_rec(expr.op0());
  }
  else if(expr.id()==ID_if)
  {
    if(expr.operands().size()==3)
    {
      bool result=true;
      if(!simplify_rec(expr.op0())) result=false;
      if(!simplify_address_of_arg(expr.op1())) result=false;
      if(!simplify_address_of_arg(expr.op2())) result=false;

      // op0 is a constant?
      if(expr.op0().is_true())
      {
        result=false;
        exprt tmp;
        tmp.swap(expr.op1());
        expr.swap(tmp);
      }
      else if(expr.op0().is_false())
      {
        result=false;
        exprt tmp;
        tmp.swap(expr.op2());
        expr.swap(tmp);
      }
      
      return result;
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_address_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_address_of(exprt &expr)
{
  if(expr.operands().size()!=1) return true;

  if(ns.follow(expr.type()).id()!=ID_pointer) return true;
  
  exprt &object=expr.op0();
  
  bool result=simplify_address_of_arg(object);
  
  if(object.id()==ID_index)
  {
    index_exprt &index_expr=to_index_expr(object);
  
    if(!index_expr.index().is_zero())
    {
      // we normalize &a[i] to (&a[0])+i
      exprt offset;
      offset.swap(index_expr.op1());
      index_expr.op1()=gen_zero(offset.type());

      exprt addition(ID_plus, expr.type());
      addition.move_to_operands(expr, offset);
      
      expr.swap(addition);
      return false;
    }
  }
  else if(object.id()==ID_dereference)
  {
    // simplify &*p to p
    assert(object.operands().size()==1);
    exprt tmp=object.op0();
    expr=tmp;
    return false;
  }

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_pointer_offset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_pointer_offset(exprt &expr)
{
  if(expr.operands().size()!=1) return true;

  exprt &ptr=expr.op0();

  if(ptr.type().id()!=ID_pointer) return true;
  
  if(ptr.id()==ID_address_of)
  {
    if(ptr.operands().size()!=1) return true;

    mp_integer offset=compute_pointer_offset(ptr.op0(), ns);

    if(offset!=-1)
    {
      expr=from_integer(offset, expr.type());
      return false;
    }    
  }
  else if(ptr.id()==ID_typecast) // pointer typecast
  {
    if(ptr.operands().size()!=1) return true;
    
    const typet &op_type=ns.follow(ptr.op0().type());
    
    if(op_type.id()==ID_pointer)
    {
      // Cast from pointer to pointer.
      // This just passes through, remove typecast.
      exprt tmp=ptr.op0();
      ptr=tmp;
    
      // recursive call
      simplify_node(expr);
      return false;
    }
    else if(op_type.id()==ID_signedbv ||
            op_type.id()==ID_unsignedbv)
    {
      // Cast from integer to pointer, say (int *)x.
      
      if(ptr.op0().is_constant())
      {
        // (T *)0x1234 -> 0x1234
        exprt tmp=ptr.op0();
        tmp.make_typecast(expr.type());
        simplify_node(tmp);
        expr.swap(tmp);
        return false;
      }
      else
      {
        // We do a bit of special treatment for (TYPE *)(a+(int)&o),
        // which is re-written to 'a'.

        typet type=ns.follow(expr.type());      
        exprt tmp=ptr.op0();
        if(tmp.id()==ID_plus && tmp.operands().size()==2)
        {
          if(tmp.op0().id()==ID_typecast &&
             tmp.op0().operands().size()==1 &&
             tmp.op0().op0().id()==ID_address_of)
          {
            expr=tmp.op1();
            if(type!=expr.type())
              expr.make_typecast(type);

            simplify_node(expr);
            return false;
          }
          else if(tmp.op1().id()==ID_typecast &&
                  tmp.op1().operands().size()==1 &&
                  tmp.op1().op0().id()==ID_address_of)
          {
            expr=tmp.op0();
            if(type!=expr.type())
              expr.make_typecast(type);

            simplify_node(expr);
            return false;
          }
        }
      }
    }
  }
  else if(ptr.id()==ID_plus) // pointer arithmetic
  {
    exprt::operandst ptr_expr;
    exprt::operandst int_expr;
    
    forall_operands(it, ptr)
    {
      if(it->type().id()==ID_pointer)
        ptr_expr.push_back(*it);
      else if(!it->is_zero())
      {
        exprt tmp=*it;
        if(tmp.type()!=expr.type())
        {
          tmp.make_typecast(expr.type());
          simplify_node(tmp);
        }
        
        int_expr.push_back(tmp);
      }
    }

    if(ptr_expr.size()!=1 || int_expr.empty())
      return true;
      
    typet pointer_type=ptr_expr.front().type();

    mp_integer element_size=
      pointer_offset_size(pointer_type.subtype(), ns);
    
    if(element_size==0) return true;
    
    // this might change the type of the pointer!
    exprt ptr_off(ID_pointer_offset, expr.type());
    ptr_off.copy_to_operands(ptr_expr.front());
    simplify_node(ptr_off);

    exprt sum;
    
    if(int_expr.size()==1)
      sum=int_expr.front();
    else
    {
      sum=exprt(ID_plus, expr.type());
      sum.operands()=int_expr;
    }
      
    simplify_node(sum);
    
    exprt size_expr=
      from_integer(element_size, expr.type());
        
    binary_exprt product(sum, ID_mult, size_expr, expr.type());
  
    simplify_node(product);
    
    expr=binary_exprt(ptr_off, ID_plus, product, expr.type());

    simplify_node(expr);
    
    return false;
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_mult

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_mult(exprt &expr)
{
  // check to see if it is a number type
  if(!is_number(expr.type()))
    return true;

  // vector of operands
  exprt::operandst &operands=expr.operands();

  // result of the simplification
  bool result = true;

  // position of the constant
  exprt::operandst::iterator constant;

  // true if we have found a constant
  bool found = false;
  
  typet c_sizeof_type=nil_typet();

  // scan all the operands
  for(exprt::operandst::iterator it=operands.begin();
      it!=operands.end();)
  {
    // if one of the operands is not a number return
    if(!is_number(it->type())) return true;

    // if one of the operands is zero the result is zero
    // note: not true on IEEE floating point arithmetic
    if(it->is_zero() &&
       it->type().id()!=ID_floatbv)
    {
      expr=gen_zero(expr.type());
      return false;
    }

    // true if the given operand has to be erased
    bool do_erase = false;

    // if this is a constant of the same time as the result
    if(it->is_constant() && it->type()==expr.type())
    {
      // preserve the sizeof type annotation
      if(c_sizeof_type.is_nil())
        c_sizeof_type=
          static_cast<const typet &>(it->find(ID_C_c_sizeof_type));

      if(found)
      {
	// update the constant factor
	if(!constant->mul(*it)) do_erase=true;
      }
      else
      {
	// set it as the constant factor if this is the first
	constant=it;
	found=true;
      }
    }

    // erase the factor if necessary
    if(do_erase)
    {
      it=operands.erase(it);
      result = false;
    }
    else
      it++; // move to the next operand
  }
  
  if(c_sizeof_type.is_not_nil())
  {
    assert(found);
    constant->set(ID_C_c_sizeof_type, c_sizeof_type);
  }

  if(operands.size()==1)
  {
    exprt product(operands.front());
    expr.swap(product);

    result = false;
  }
  else
  {
    // if the constant is a one and there are other factors
    if(found && constant->is_one())
    {
      // just delete it
      operands.erase(constant);
      result=false;

      if(operands.size()==1)
      {
        exprt product(operands.front());
        expr.swap(product);
      }
    }
  }

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_div

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_div(exprt &expr)
{
  if(!is_number(expr.type()))
    return true;

  if(expr.operands().size()!=2)
    return true;
    
  const typet &expr_type=expr.type();

  if(expr_type!=expr.op0().type() ||
     expr_type!=expr.op1().type())
    return true;

  if(expr_type.id()==ID_signedbv ||
     expr_type.id()==ID_unsignedbv ||
     expr_type.id()==ID_natural ||
     expr_type.id()==ID_integer)
  {
    mp_integer int_value0, int_value1;
    bool ok0, ok1;

    ok0=!to_integer(expr.op0(), int_value0);
    ok1=!to_integer(expr.op1(), int_value1);

    // division by zero?
    if(ok1 && int_value1==0)
      return true;

    // x/1?
    if(ok1 && int_value1==1)
    {
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
      return false;
    }

    // 0/x?
    if(ok0 && int_value0==0)
    {
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
      return false;
    }

    if(ok0 && ok1)
    {
      mp_integer result=int_value0/int_value1;
      exprt tmp=from_integer(result, expr_type);

      if(tmp.is_not_nil())
      {
        expr.swap(tmp);
        return false;
      }
    }
  }
  else if(expr_type.id()==ID_rational)
  {
    rationalt rat_value0, rat_value1;
    bool ok0, ok1;

    ok0=!to_rational(expr.op0(), rat_value0);
    ok1=!to_rational(expr.op1(), rat_value1);

    if(ok1 && rat_value1.is_zero())
      return true;

    if((ok1 && rat_value1.is_one()) ||
       (ok0 && rat_value0.is_zero()))
    {
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
      return false;
    }

    if(ok0 && ok1)
    {
      rationalt result=rat_value0/rat_value1;
      exprt tmp=from_rational(result);

      if(tmp.is_not_nil())
      {
        expr.swap(tmp);
        return false;
      }
    }
  }
  else if(expr_type.id()==ID_fixedbv)
  {
    // division by one?
    if(expr.op1().is_constant() &&
       expr.op1().is_one())
    {
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
      return false;
    }

    if(expr.op0().is_constant() &&
       expr.op1().is_constant())
    {
      fixedbvt f0(to_constant_expr(expr.op0()));
      fixedbvt f1(to_constant_expr(expr.op1()));
      if(!f1.is_zero())
      {
        f0/=f1;
        expr=f0.to_expr();
        return false;
      }
    }
  }
  else if(expr_type.id()==ID_floatbv)
  {
    // division by one?
    if(expr.op1().is_constant() &&
       expr.op1().is_one())
    {
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
      return false;
    }

    if(expr.op0().is_constant() &&
       expr.op1().is_constant())
    {
      ieee_floatt f0(to_constant_expr(expr.op0()));
      ieee_floatt f1(to_constant_expr(expr.op1()));
      f0/=f1;
      expr=f0.to_expr();
      return false;
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_mod

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_mod(exprt &expr)
{
  if(!is_number(expr.type()))
    return true;

  if(expr.operands().size()!=2)
    return true;

  if(expr.type().id()==ID_signedbv ||
     expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_natural ||
     expr.type().id()==ID_integer)
  {
    if(expr.type()==expr.op0().type() &&
       expr.type()==expr.op1().type())
    {
      mp_integer int_value0, int_value1;
      bool ok0, ok1;

      ok0=!to_integer(expr.op0(), int_value0);
      ok1=!to_integer(expr.op1(), int_value1);

      if(ok1 && int_value1==0)
        return true; // division by zero

      if((ok1 && int_value1==1) ||
         (ok0 && int_value0==0))
      {
        expr=gen_zero(expr.type());
        return false;
      }

      if(ok0 && ok1)
      {
        mp_integer result=int_value0%int_value1;
        exprt tmp=from_integer(result, expr.type());

        if(tmp.is_not_nil())
        {
          expr.swap(tmp);
          return false;
        }
      }
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_plus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_plus(exprt &expr)
{
  if(!is_number(expr.type()) &&
     expr.type().id()!=ID_pointer)
    return true;

  bool result=true;

  exprt::operandst &operands=expr.operands();
  
  assert(expr.id()==ID_plus);

  // floating-point addition is _NOT_ associative; thus,
  // there is special case for float
  
  if(ns.follow(expr.type()).id()==ID_floatbv)
  {
    // we only merge neighboring constants!
    Forall_expr(it, operands)
    {
      exprt::operandst::iterator next=it;
      next++;
      
      if(next!=operands.end())
      {
        if(it->type()==next->type() &&
           it->is_constant() &&
           next->is_constant())
        {
          it->sum(*next);
          operands.erase(next);
        }
      }
    }
  }
  else
  {
    // count the constants
    size_t count=0;
    forall_operands(it, expr)
      if(is_number(it->type()) && it->is_constant())
        count++;
    
    // merge constants?
    if(count>=2)
    {
      exprt::operandst::iterator const_sum;
      bool const_sum_set=false;

      Forall_operands(it, expr)
      {
        if(is_number(it->type()) && it->is_constant())
        {
          if(!const_sum_set)
          {
            const_sum=it;
            const_sum_set=true;
          }
          else
          {
            if(!const_sum->sum(*it))
            {
              *it=gen_zero(it->type());
              result=false;
            }
          }
        }
      }
    }
    
    // search for a and -a
    // first gather all the a's with -a
    typedef hash_map_cont<exprt, exprt::operandst::iterator, irep_hash>
      expr_mapt;
    expr_mapt expr_map;

    Forall_expr(it, operands)
      if(it->id()==ID_unary_minus &&
         it->operands().size()==1)
        expr_map.insert(std::make_pair(it->op0(), it));

    // now search for a
    Forall_expr(it, operands)
    {
      if(expr_map.empty()) break;
      else if(it->id()==ID_unary_minus) continue;

      expr_mapt::iterator itm=expr_map.find(*it);

      if(itm!=expr_map.end())
      {
        *(itm->second)=gen_zero(expr.type());
        *it=gen_zero(expr.type());
        expr_map.erase(itm);
        result=false;
      }
    }

    // delete zeros
    // (can't do for floats, as the result of 0.0 + (-0.0)
    // need not be -0.0 in std rounding)
    for(exprt::operandst::iterator
        it=operands.begin();
        it!=operands.end();
        /* no it++ */)
    {
      if(is_number(it->type()) && it->is_zero())
      {
        it=operands.erase(it);
        result=false;
      }
      else
        it++;
    }
  }

  if(operands.empty())
  {
    expr=gen_zero(expr.type());
    return false;
  }
  else if(operands.size()==1)
  {
    exprt tmp(operands.front());
    expr.swap(tmp);
    return false;
  }

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_minus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_minus(exprt &expr)
{
  if(!is_number(expr.type()) &&
     expr.type().id()!=ID_pointer)
    return true;

  exprt::operandst &operands=expr.operands();

  assert(expr.id()==ID_minus);

  if(operands.size()!=2)
    return true;
  
  if(is_number(expr.type()) &&
     is_number(operands[0].type()) &&
     is_number(operands[1].type()))
  {
    // rewrite "a-b" to "a+(-b)"
    unary_minus_exprt tmp2(operands[1]);
    simplify_unary_minus(tmp2);

    plus_exprt tmp(operands[0], tmp2);
    simplify_plus(tmp);

    expr.swap(tmp);
    return false;
  }
  else if(expr.type().id()==ID_pointer &&
          operands[0].type().id()==ID_pointer &&
          is_number(operands[1].type()))
  {
    // pointer arithmetic: rewrite "p-i" to "p+(-i)"
    unary_minus_exprt tmp2(operands[1]);
    simplify_unary_minus(tmp2);

    plus_exprt tmp(operands[0], tmp2);
    simplify_plus(tmp);

    expr.swap(tmp);
    return false;
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_floatbv_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_floatbv_typecast(exprt &expr)
{
  // These casts usually reduce precision, and thus, usually round.

  assert(expr.operands().size()==2);
        
  const typet &dest_type=ns.follow(expr.type());
  const typet &src_type=ns.follow(expr.op0().type());

  // eliminate redundant casts
  if(dest_type==src_type)
  {
    expr=expr.op0();
    return false;
  }
  
  if(dest_type.id()!=ID_floatbv)
    return true;
    
  exprt op0=expr.op0();
  exprt op1=expr.op1(); // rounding mode
  
  // We can soundly re-write (float)((double)x op (double)y)
  // to x op y. True for any rounding mode!

  #if 0
  if(op0.id()==ID_floatbv_div ||
     op0.id()==ID_floatbv_mult ||
     op0.id()==ID_floatbv_plus ||
     op0.id()==ID_floatbv_minus)
  {
    if(op0.operands().size()==3 &&
       op0.op0().id()==ID_typecast &&
       op0.op1().id()==ID_typecast &&
       op0.op0().operands().size()==1 &&
       op0.op1().operands().size()==1 &&
       ns.follow(op0.op0().type())==dest_type &&
       ns.follow(op0.op1().type())==dest_type)
    {
      exprt result(op0.id(), expr.type());
      result.operands().resize(3);
      result.op0()=op0.op0().op0();
      result.op1()=op0.op1().op0();
      result.op2()=op1;

      simplify_node(result);
      expr.swap(result);
      return false;
    }
  }
  #endif

  // constant folding  
  if(op0.is_constant() && op1.is_constant())
  {
    mp_integer rounding_mode;
    if(!to_integer(op1, rounding_mode))
    {
      if(src_type.id()==ID_floatbv)
      {
        ieee_floatt result(to_constant_expr(op0));
        result.rounding_mode=(ieee_floatt::rounding_modet)integer2long(rounding_mode);
        result.change_spec(to_floatbv_type(dest_type));
        expr=result.to_expr();
        return false;
      }
      else if(src_type.id()==ID_signedbv ||
              src_type.id()==ID_unsignedbv)
      {
        mp_integer value;
        if(!to_integer(op0, value))
        {
          ieee_floatt result;
          result.rounding_mode=(ieee_floatt::rounding_modet)integer2long(rounding_mode);
          result.spec=to_floatbv_type(dest_type);
          result.from_integer(value);
          expr=result.to_expr();
          return false;
        }
      }
    }
  }

  #if 0
  // (T)(a?b:c) --> a?(T)b:(T)c
  if(expr.op0().id()==ID_if &&
     expr.op0().operands().size()==3)
  {
    exprt tmp_op1=binary_exprt(expr.op0().op1(), ID_floatbv_typecast, expr.op1(), dest_type);
    exprt tmp_op2=binary_exprt(expr.op0().op2(), ID_floatbv_typecast, expr.op1(), dest_type);
    simplify_floatbv_typecast(tmp_op1);
    simplify_floatbv_typecast(tmp_op2);
    expr=if_exprt(expr.op0().op0(), tmp_op1, tmp_op2, dest_type);
    simplify_if(expr);
    return false;
  }
  #endif
  
  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_floatbv_op

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_floatbv_op(exprt &expr)
{
  const typet &type=ns.follow(expr.type());
  
  if(type.id()!=ID_floatbv)
    return true;

  assert(expr.operands().size()==3);
  
  exprt op0=expr.op0();
  exprt op1=expr.op1();
  exprt op2=expr.op2(); // rounding mode

  assert(ns.follow(op0.type())==type);
  assert(ns.follow(op1.type())==type);

  // Remember that floating-point addition is _NOT_ associative.
  // Thus, we don't re-sort the operands.  
  // We only merge constants!
  
  if(op0.is_constant() && op1.is_constant() && op2.is_constant())
  {
    ieee_floatt v0(to_constant_expr(op0));
    ieee_floatt v1(to_constant_expr(op1));

    mp_integer rounding_mode;
    if(!to_integer(op2, rounding_mode))
    {
      v0.rounding_mode=(ieee_floatt::rounding_modet)integer2long(rounding_mode);
      v1.rounding_mode=v0.rounding_mode;
      
      ieee_floatt result=v0;
      
      if(expr.id()==ID_floatbv_plus)
        result+=v1;
      else if(expr.id()==ID_floatbv_minus)
        result-=v1;
      else if(expr.id()==ID_floatbv_mult)
        result*=v1;
      else if(expr.id()==ID_floatbv_div)
        result/=v1;
      else
        assert(false);

      expr=result.to_expr();
      return false;
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_bitwise

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_bitwise(exprt &expr)
{
  if(!is_bitvector_type(expr.type()))
    return true;
    
  // check if these are really boolean
  if(expr.type().id()!=ID_bool)
  {
    bool all_bool=true;
    
    forall_operands(it, expr)
    {
      if(it->id()==ID_typecast &&
         it->operands().size()==1 &&
         ns.follow(it->op0().type()).id()==ID_bool)
      {
      }
      else if(it->is_zero() || it->is_one())
      {
      }
      else
        all_bool=false;
    }
        
    if(all_bool)
    {
      // re-write to boolean+typecast
      exprt new_expr=expr;
      
      if(expr.id()==ID_bitand)
        new_expr.id(ID_and);
      else if(expr.id()==ID_bitor)
        new_expr.id(ID_or);
      else if(expr.id()==ID_bitxor)
        new_expr.id(ID_xor);
      else
        assert(false);
        
      Forall_operands(it, new_expr)
      {
        if(it->id()==ID_typecast)
        {
          exprt tmp;
          tmp=it->op0();
          it->swap(tmp);
        }
        else if(it->is_zero())
          *it=false_exprt();
        else if(it->is_one())
          *it=true_exprt();
      }
        
      new_expr.type()=bool_typet();
      simplify_node(new_expr);

      new_expr.make_typecast(expr.type());
      simplify_node(new_expr);
      
      expr.swap(new_expr);
      return false;
    }
  }

  bool result=true;
    
  // try to merge constants
  
  unsigned width=to_bitvector_type(expr.type()).get_width();
    
  while(expr.operands().size()>=2)
  {
    const irep_idt &a_str=expr.op0().get(ID_value);
    const irep_idt &b_str=expr.op1().get(ID_value);
    
    if(!expr.op0().is_constant())
      break;
      
    if(!expr.op1().is_constant())
      break;
      
    if(expr.op0().type()!=expr.type())
      break;
                
    if(expr.op1().type()!=expr.type())
      break;
      
    assert(a_str.size()==b_str.size());
      
    constant_exprt new_op(expr.type());
    std::string new_value;
    new_value.resize(width);
                
    if(expr.id()==ID_bitand)
    {
      for(unsigned i=0; i<width; i++)
        new_value[i]=(a_str[i]=='1' && b_str[i]=='1')?'1':'0';
    }
    else if(expr.id()==ID_bitor)
    {
      for(unsigned i=0; i<width; i++)
        new_value[i]=(a_str[i]=='1' || b_str[i]=='1')?'1':'0';
    }
    else if(expr.id()==ID_bitxor)
    {
      for(unsigned i=0; i<width; i++)
        new_value[i]=((a_str[i]=='1')!=(b_str[i]=='1'))?'1':'0';
    }
    else
      break;
      
    new_op.set_value(new_value);

    // erase first operand
    expr.operands().erase(expr.operands().begin());
    expr.op0().swap(new_op);
    
    result=false;
  }

  // now erase zeros out of bitor, bitxor

  if(expr.id()==ID_bitor || expr.id()==ID_bitxor)
  {
    for(exprt::operandst::iterator
        it=expr.operands().begin();
        it!=expr.operands().end();
        ) // no it++
    {
      if(it->is_zero() && expr.operands().size()>1)
      {
        it=expr.operands().erase(it);
        result=false;
      }
      else
        it++;
    }
  }
  
  // two operands that are syntactically the same

  if(expr.operands().size()==2 &&
     expr.op0()==expr.op1())
  {
    if(expr.id()==ID_bitand || expr.id()==ID_bitor)
    {
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
      return false;
    }
    else if(expr.id()==ID_bitxor)
    {
      constant_exprt new_op(expr.type());
      new_op.set_value(integer2binary(0, width));
      expr.swap(new_op);
      return false;
    }
  }
  
  if(expr.operands().size()==1)
  {
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
    return false;
  }
  
  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_extractbit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_extractbit(exprt &expr)
{
  const typet &op0_type=expr.op0().type();

  if(!is_bitvector_type(op0_type))
    return true;
  
  unsigned width=to_bitvector_type(op0_type).get_width();

  assert(expr.operands().size()==2);

  mp_integer i;

  if(to_integer(expr.op1(), i))
    return true;

  if(!expr.op0().is_constant())
    return true;

  if(i<0 || i>=width)
    return true;

  const irep_idt &value=expr.op0().get(ID_value);

  if(value.size()!=width)
    return true;

  bool bit=(id2string(value)[width-integer2long(i)-1]=='1');

  expr.make_bool(bit);

  return false;
}

/*******************************************************************\

Function: simplify_exprt::simplify_concatenation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_concatenation(exprt &expr)
{
  bool result=true;

  if(is_bitvector_type(expr.type()))
  {
    // first, turn bool into bvec[1]
    Forall_operands(it, expr)
    {
      exprt &op=*it;
      if(op.is_true() || op.is_false())
      {
        bool value=op.is_true();
        op=constant_exprt(value?ID_1:ID_0, unsignedbv_typet(1));
      }
    }
    
    // search for neighboring constants to merge
    size_t i=0;
    
    while(i<expr.operands().size()-1)
    {
      exprt &opi=expr.operands()[i];
      exprt &opn=expr.operands()[i+1];
    
      if(opi.is_constant() &&
         opn.is_constant() &&
         is_bitvector_type(opi.type()) &&
         is_bitvector_type(opn.type()))
      {
        // merge!
        const std::string new_value=
          opi.get_string(ID_value)+opn.get_string(ID_value);
        opi.set(ID_value, new_value);
        opi.type().set(ID_width, new_value.size());
        // erase opn
        expr.operands().erase(expr.operands().begin()+i+1);
        result=true;
      }
      else
        i++;
    }
  }
  else if(expr.type().id()==ID_verilogbv)
  {
    // search for neighboring constants to merge
    size_t i=0;
    
    while(i<expr.operands().size()-1)
    {
      exprt &opi=expr.operands()[i];
      exprt &opn=expr.operands()[i+1];
    
      if(opi.is_constant() &&
         opn.is_constant() &&
         (opi.type().id()==ID_verilogbv || is_bitvector_type(opi.type())) &&
         (opn.type().id()==ID_verilogbv || is_bitvector_type(opn.type())))
      {
        // merge!
        const std::string new_value=
          opi.get_string(ID_value)+opn.get_string(ID_value);
        opi.set(ID_value, new_value);
        opi.type().set(ID_width, new_value.size());
        opi.type().id(ID_verilogbv);
        // erase opn
        expr.operands().erase(expr.operands().begin()+i+1);
        result=true;
      }
      else
        i++;
    }
  }

  // { x } = x
  if(expr.operands().size()==1)
  {
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
    result=false;
  }
  
  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_shifts

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_shifts(exprt &expr)
{
  if(!is_number(expr.type()))
    return true;

  if(expr.operands().size()!=2)
    return true;

  mp_integer distance;
  
  if(to_integer(expr.op1(), distance))
    return true;
    
  if(distance==0)
  {
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
    return false;
  }

  mp_integer value;
  
  if(to_integer(expr.op0(), value))
    return true;

  if(expr.op0().type().id()==ID_unsignedbv || 
     expr.op0().type().id()==ID_signedbv)
  { 
    mp_integer width=
      string2integer(id2string(expr.op0().type().get(ID_width)));
      
    if(expr.id()==ID_lshr)
    {
      // this is to guard against large values of distance
      if(distance>=width)
      {
        expr=gen_zero(expr.type());
        return false;
      }
      else if(distance>=0)
      {
        value/=power(2, distance);
        expr=from_integer(value, expr.type());
        return false;
      }
    }
    else if(expr.id()==ID_ashr)
    {
      if(distance>=0)
      {
        // this is to simulate an arithmetic right shift
        mp_integer new_value=value >> distance;
        expr=from_integer(new_value, expr.type());
        return false;
      }
    }
    else if(expr.id()==ID_shl)
    {
      // this is to guard against large values of distance
      if(distance>=width)
      {
        expr=gen_zero(expr.type());
        return false;
      }
      else if(distance>=0)
      {
        value*=power(2, distance);
        expr=from_integer(value, expr.type());
        return false;
      }
    }
  }
  else if(expr.op0().type().id()==ID_integer ||
	  expr.op0().type().id()==ID_natural)
  {
    if(expr.id()==ID_lshr)
    {
      if(distance>=0)
      {
        value/=power(2, distance);
        expr=from_integer(value, expr.type());
        return false;
      }
    }
    else if(expr.id()==ID_ashr)
    {
      // this is to simulate an arithmetic right shift
      if(distance>=0)
      {
        mp_integer new_value=value/power(2, distance);
        if(value<0 && new_value==0) new_value=-1;

        expr=from_integer(new_value, expr.type());
        return false;
      }
    }
    else if(expr.id()==ID_shl)
    {
      if(distance>=0)
      {
        value*=power(2, distance);
        expr=from_integer(value, expr.type());
        return false;
      }
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_if_implies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_if_implies(
  exprt &expr,
  const exprt &cond,
  bool truth,
  bool &new_truth)
{
  if(expr == cond)
  {
    new_truth = truth;
    return false;
  }

  if(truth && cond.id()==ID_lt && expr.id()==ID_lt)
  {
    if(cond.op0() == expr.op0() &&
	cond.op1().is_constant() &&
	expr.op1().is_constant() &&
	cond.op1().type() == expr.op1().type())
    {
      const irep_idt &type_id = cond.op1().type().id();
      if(type_id==ID_integer || type_id==ID_natural)
      {
	if(string2integer(cond.op1().get_string(ID_value)) >=
	  string2integer(expr.op1().get_string(ID_value)))
        {
	  new_truth = true;
	  return false;
        }
      }
      else if(type_id==ID_unsignedbv)
      {
	const mp_integer i1, i2;
	if(binary2integer(cond.op1().get_string(ID_value), false) >=
           binary2integer(expr.op1().get_string(ID_value), false))
        {
	  new_truth = true;
	  return false;
        }
      }
      else if(type_id==ID_signedbv)
      {
	const mp_integer i1, i2;
	if(binary2integer(cond.op1().get_string(ID_value), true) >=
           binary2integer(expr.op1().get_string(ID_value), true))
        {
	  new_truth = true;
	  return false;
        }
      }
    }
    if(cond.op1() == expr.op1() &&
	cond.op0().is_constant() &&
	expr.op0().is_constant() &&
	cond.op0().type() == expr.op0().type())
    {
      const irep_idt &type_id = cond.op1().type().id();
      if(type_id==ID_integer || type_id==ID_natural)
      {
	if(string2integer(cond.op1().get_string(ID_value)) <=
           string2integer(expr.op1().get_string(ID_value)))
        {
	  new_truth = true;
	  return false;
        }
      }
      else if(type_id==ID_unsignedbv)
      {
	const mp_integer i1, i2;
	if(binary2integer(cond.op1().get_string(ID_value), false) <=
           binary2integer(expr.op1().get_string(ID_value), false))
        {
	  new_truth = true;
	  return false;
        }
      }
      else if(type_id==ID_signedbv)
      {
	const mp_integer i1, i2;
	if(binary2integer(cond.op1().get_string(ID_value), true) <=
           binary2integer(expr.op1().get_string(ID_value), true))
        {
	  new_truth = true;
	  return false;
        }
      }
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_if_recursive

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_if_recursive(
  exprt &expr,
  const exprt &cond,
  bool truth)
{
  if(expr.type().id()==ID_bool)
  {
    bool new_truth;

    if(!simplify_if_implies(expr, cond, truth, new_truth))
    {
      if(new_truth)
      {
	expr=true_exprt();
	return false;
      }
      else
      {
	expr=false_exprt();
	return false;
      }
    }
  }

  bool result = true;

  Forall_operands(it, expr)
    result = simplify_if_recursive(*it, cond, truth) && result;

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_if_conj

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_if_conj(
  exprt &expr,
  const exprt &cond)
{
  forall_operands(it, cond)
  {
    if(expr == *it)
    {
      expr=true_exprt();
      return false;
    }
  }

  bool result = true;

  Forall_operands(it, expr)
    result = simplify_if_conj(*it, cond) && result;

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_if_disj

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_if_disj(
  exprt &expr,
  const exprt &cond)
{
  forall_operands(it, cond)
  {
    if(expr == *it)
    {
      expr=false_exprt();
      return false;
    }
  }

  bool result = true;

  Forall_operands(it, expr)
    result = simplify_if_disj(*it, cond) && result;

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_if_branch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_if_branch(
  exprt &trueexpr,
  exprt &falseexpr,
  const exprt &cond)
{
  bool tresult = true;
  bool fresult = true;

  if(cond.id()==ID_and)
  {
    tresult = simplify_if_conj(trueexpr, cond) && tresult;
    fresult = simplify_if_recursive(falseexpr, cond, false) && fresult;
  }
  else if(cond.id()==ID_or)
  {
    tresult = simplify_if_recursive(trueexpr, cond, true) && tresult;
    fresult = simplify_if_disj(falseexpr, cond) && fresult;
  }
  else
  {
    tresult = simplify_if_recursive(trueexpr, cond, true) && tresult;
    fresult = simplify_if_recursive(falseexpr, cond, false) && fresult;
  }

  if(!tresult) simplify_rec(trueexpr);
  if(!fresult) simplify_rec(falseexpr);

  return tresult && fresult;
}

/*******************************************************************\

Function: simplify_exprt::simplify_if_cond

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_if_cond(exprt &expr)
{
  bool result = true;
  bool tmp = false;

  while(!tmp)
  {
    tmp = true;

    if(expr.id()==ID_and)
    {
      if(expr.has_operands())
      {
	exprt::operandst &operands = expr.operands();
	for(exprt::operandst::iterator it1 = operands.begin();
	    it1 != operands.end(); it1++)
        {
	  for(exprt::operandst::iterator it2 = operands.begin();
	      it2 != operands.end(); it2++)
          {
	    if(it1 != it2)
	      tmp = simplify_if_recursive(*it1, *it2, true) && tmp;
          }
        }
      }
    }

    if(!tmp) simplify_rec(expr);

    result = tmp && result;
  }

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_if(exprt &expr)
{
  exprt::operandst &operands=expr.operands();
  if(operands.size()!=3) return true;

  exprt &cond=operands[0];
  exprt &truevalue=operands[1];
  exprt &falsevalue=operands[2];

  if(truevalue==falsevalue)
  {
    exprt tmp;
    tmp.swap(truevalue);
    expr.swap(tmp);
    return false;
  }

  bool result=true;

  if(do_simplify_if)
  {
    if(cond.id()==ID_not)
    {
      exprt tmp;
      tmp.swap(cond.op0());
      cond.swap(tmp);
      truevalue.swap(falsevalue);
      result=false;
    }

    #if 0
    result = simplify_if_cond(cond) && result;
    result = simplify_if_branch(truevalue, falsevalue, cond) && result;
    #endif

    if(expr.type()==bool_typet())
    {
      // a?b:c <-> (a && b) || (!a && c)
    
      if(truevalue.is_true() && falsevalue.is_false())
      {
        // a?1:0 <-> a
        exprt tmp;
        tmp.swap(cond);
        expr.swap(tmp);
        return false;
      }
      else if(truevalue.is_false() && falsevalue.is_true())
      {
        // a?0:1 <-> !a
        exprt tmp;
        tmp.swap(cond);
        tmp.make_not();
        simplify_node(tmp);
        expr.swap(tmp);
        return false;
      }
      else if(falsevalue.is_false())
      {
        // a?b:0 <-> a AND b
        and_exprt tmp(cond, truevalue);
        simplify_node(tmp);
        expr.swap(tmp);
        return false;
      }
      else if(falsevalue.is_true())
      {
        // a?b:1 <-> !a OR b
        or_exprt tmp(cond, truevalue);
        tmp.op0().make_not();
        simplify_node(tmp.op0());
        simplify_node(tmp);
        expr.swap(tmp);
        return false;
      }
      else if(truevalue.is_true())
      {
        // a?1:b <-> a||(!a && b) <-> a OR b
        or_exprt tmp(cond, falsevalue);
        simplify_node(tmp);
        expr.swap(tmp);
        return false;
      }
      else if(truevalue.is_false())
      {
        // a?0:b <-> !a && b
        and_exprt tmp(cond, falsevalue);
        tmp.op0().make_not();
        simplify_node(tmp.op0());
        simplify_node(tmp);
        expr.swap(tmp);
        return false;
      }
    }

    #if 0
    // a ? b : c  --> a ? b[a/true] : c
    exprt tmp_true=truevalue;
    replace_expr(cond, true_exprt(), tmp_true);
    if(tmp_true!=truevalue)
    { truevalue=tmp_true; simplify_rec(truevalue); result=false; }

    // a ? b : c  --> a ? b : c[a/false]
    exprt tmp_false=falsevalue;
    replace_expr(cond, false_exprt(), tmp_false);
    if(tmp_false!=falsevalue)
    { falsevalue=tmp_false; simplify_rec(falsevalue); result=false; }
    #endif
  }

  if(cond.is_true())
  {
    exprt tmp;
    tmp.swap(truevalue);
    expr.swap(tmp);
    return false;
  }

  if(cond.is_false())
  {
    exprt tmp;
    tmp.swap(falsevalue);
    expr.swap(tmp);
    return false;
  }

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_not

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_not(exprt &expr)
{
  if(expr.operands().size()!=1) return true;

  exprt &op=expr.op0();

  if(expr.type().id()!=ID_bool ||
     op.type().id()!=ID_bool) return true;
     
  if(op.id()==ID_not) // (not not a) == a
  {
    if(op.operands().size()==1)
    {
      exprt tmp;
      tmp.swap(op.op0());
      expr.swap(tmp);
      return false;
    }
  }
  else if(op.is_false())
  {
    expr=true_exprt();
    return false;
  }
  else if(op.is_true())
  {
    expr=false_exprt();
    return false;
  }
  else if(op.id()==ID_and ||
          op.id()==ID_or)
  {
    exprt tmp;
    tmp.swap(op);
    expr.swap(tmp);

    Forall_operands(it, expr)
    {
      it->make_not();
      simplify_node(*it);
    }
    
    expr.id(expr.id()==ID_and?ID_or:ID_and);

    return false;
  }
  else if(op.id()==ID_notequal) // !(a!=b) <-> a==b
  {
    exprt tmp;
    tmp.swap(op);
    expr.swap(tmp);
    expr.id(ID_equal);
    return false;
  }
  
  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_boolean

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_boolean(exprt &expr)
{
  if(!expr.has_operands()) return true;

  exprt::operandst &operands=expr.operands();

  if(expr.type().id()!=ID_bool) return true;

  if(expr.id()==ID_implies)
  {
    if(operands.size()!=2 ||
       operands.front().type().id()!=ID_bool ||
       operands.back().type().id()!=ID_bool)
      return true;
      
    // turn a => b into !a || b

    expr.id(ID_or);
    expr.op0().make_not();
    simplify_node(expr.op0());
    simplify_node(expr);
    return false;
  }
  else if(expr.id()=="<=>")
  {
    if(operands.size()!=2 ||
       operands.front().type().id()!=ID_bool ||
       operands.back().type().id()!=ID_bool)
      return true;

    if(operands.front().is_false())
    {
      expr.id(ID_not);
      operands.erase(operands.begin());
      return false;
    }
    else if(operands.front().is_true())
    {
      exprt tmp(operands.back());
      expr.swap(tmp);
      return false;
    }
    else if(operands.back().is_false())
    {
      expr.id(ID_not);
      operands.erase(++operands.begin());
      return false;
    }
    else if(operands.back().is_true())
    {
      exprt tmp(operands.front());
      expr.swap(tmp);
      return false;
    }    
  }
  else if(expr.id()==ID_or ||
          expr.id()==ID_and ||
          expr.id()==ID_xor)
  {
    if(operands.empty()) return true;

    bool result=true;

    exprt::operandst::const_iterator last;
    bool last_set=false;

    bool negate=false;

    for(exprt::operandst::iterator it=operands.begin();
        it!=operands.end();)
    {
      if(it->type().id()!=ID_bool) return true;

      bool is_true=it->is_true();
      bool is_false=it->is_false();

      if(expr.id()==ID_and && is_false)
      {
        expr=false_exprt();
        return false;
      }
      else if(expr.id()==ID_or && is_true)
      {
        expr=true_exprt();
        return false;
      }

      bool erase;

      if(expr.id()==ID_and)
        erase=is_true;
      else if(is_true && expr.id()==ID_xor)
      {
        erase=true;
        negate=!negate;
      }
      else
        erase=is_false;

      if(last_set && *it==*last &&
         (expr.id()==ID_or || expr.id()==ID_and))
        erase=true; // erase duplicate operands

      if(erase)
      {
        it=operands.erase(it);
        result=false;
      }
      else
      {
        last=it;
        last_set=true;
        it++;
      }
    }
    
    // search for a and !a
    if(expr.id()==ID_and || expr.id()==ID_or)
    {
      // first gather all the a's with !a

      hash_set_cont<exprt, irep_hash> expr_set;

      forall_operands(it, expr)
        if(it->id()==ID_not &&
           it->operands().size()==1 &&
           it->type().id()==ID_bool)
          expr_set.insert(it->op0());

      // now search for a

      if(!expr_set.empty())
        forall_operands(it, expr)
        {
          if(it->id()!=ID_not &&
             expr_set.find(*it)!=expr_set.end())
          {
            expr.make_bool(expr.id()==ID_or);
            return false;
          }
        }
    }

    if(operands.empty())
    {
      if(expr.id()==ID_and || negate)
        expr=true_exprt();
      else
        expr=false_exprt();

      return false;
    }
    else if(operands.size()==1)
    {
      if(negate)
        expr.op0().make_not();
      exprt tmp(operands.front());
      expr.swap(tmp);
      return false;
    }

    return result;
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_bitnot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_bitnot(exprt &expr)
{
  if(!expr.has_operands()) return true;

  exprt::operandst &operands=expr.operands();

  if(operands.size()!=1) return true;

  exprt &op=operands.front();

  if(expr.type().id()==ID_bv ||
     expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv)
  {
    if(op.type()==expr.type())
    {
      if(op.id()==ID_constant)
      {
        std::string value=op.get_string(ID_value);

        for(std::string::iterator it=value.begin();
            it!=value.end();
            ++it)
          *it=(*it=='0')?'1':'0';

        exprt tmp(ID_constant, op.type());
        tmp.set(ID_value, value);
        expr.swap(tmp);
        return false;
      }
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::get_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::get_values(
  const exprt &expr,
  value_listt &value_list)
{
  if(expr.is_constant())
  {
    mp_integer int_value;
    if(to_integer(expr, int_value))
      return true;

    value_list.insert(int_value);

    return false;
  }
  else if(expr.id()==ID_if)
  {
    if(expr.operands().size()!=3)
      return true;

    return get_values(expr.op1(), value_list) ||
           get_values(expr.operands().back(), value_list);
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_inequality_address_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_inequality_address_of(exprt &expr)
{
  assert(expr.type().id()==ID_bool);
  assert(expr.operands().size()==2);
  assert(expr.id()==ID_equal || expr.id()==ID_notequal);

  exprt tmp0=expr.op0();
  if(tmp0.id()==ID_typecast)
    tmp0=expr.op0().op0();
  if(tmp0.op0().id()==ID_index &&
     to_index_expr(tmp0.op0()).index().is_zero())
    tmp0=address_of_exprt(to_index_expr(tmp0.op0()).array());
  exprt tmp1=expr.op1();
  if(tmp1.id()==ID_typecast)
    tmp1=expr.op1().op0();
  if(tmp1.op0().id()==ID_index &&
     to_index_expr(tmp1.op0()).index().is_zero())
    tmp1=address_of_exprt(to_index_expr(tmp1.op0()).array());
  assert(tmp0.id()==ID_address_of);
  assert(tmp1.id()==ID_address_of);

  if(tmp0.operands().size()!=1) return true;
  if(tmp1.operands().size()!=1) return true;
  
  if(tmp0.op0().id()==ID_symbol &&
     tmp1.op0().id()==ID_symbol)
  {
    bool equal=
       tmp0.op0().get(ID_identifier)==
       tmp1.op0().get(ID_identifier);
       
    expr.make_bool(expr.id()==ID_equal?equal:!equal);
    
    return false;
  }
  
  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_inequality

  Inputs:

 Outputs:

 Purpose: simplifies inequalities !=, <=, <, >=, >, and also ==

\*******************************************************************/

bool simplify_exprt::simplify_inequality(exprt &expr)
{
  exprt::operandst &operands=expr.operands();

  if(expr.type().id()!=ID_bool) return true;

  if(operands.size()!=2) return true;

  exprt tmp0=expr.op0();
  exprt tmp1=expr.op1();
  
  // types must match
  if(!base_type_eq(tmp0.type(), tmp1.type(), ns))
    return true;
    
  // see if we are comparing pointers that are address_of
  if((tmp0.id()==ID_address_of ||
        (tmp0.id()==ID_typecast && tmp0.op0().id()==ID_address_of)) &&
      (tmp1.id()==ID_address_of ||
       (tmp1.id()==ID_typecast && tmp1.op0().id()==ID_address_of)) &&
      (expr.id()==ID_equal || expr.id()==ID_notequal))
    return simplify_inequality_address_of(expr);

  // first see if we compare to a constant
  
  bool op0_is_const=tmp0.is_constant();
  bool op1_is_const=tmp1.is_constant();
  
  ns.follow_symbol(tmp0.type());
  ns.follow_symbol(tmp1.type());
  
  if(tmp0.type().id()==ID_c_enum_tag)
    tmp0.type()=ns.follow_tag(to_c_enum_tag_type(tmp0.type()));

  if(tmp1.type().id()==ID_c_enum_tag)
    tmp1.type()=ns.follow_tag(to_c_enum_tag_type(tmp1.type()));

  // are _both_ constant?  
  if(op0_is_const && op1_is_const)
  {
    if(tmp0.type().id()==ID_bool)
    {
      bool v0=tmp0.is_true();
      bool v1=tmp1.is_true();

      if(expr.id()==ID_equal)
      {
        expr.make_bool(v0==v1);
        return false;
      }
      else if(expr.id()==ID_notequal)
      {
        expr.make_bool(v0!=v1);
        return false;
      }
    }
    else if(tmp0.type().id()==ID_fixedbv)
    {
      fixedbvt f0(to_constant_expr(tmp0));
      fixedbvt f1(to_constant_expr(tmp1));

      if(expr.id()==ID_notequal)
        expr.make_bool(f0!=f1);
      else if(expr.id()==ID_equal)
        expr.make_bool(f0==f1);
      else if(expr.id()==ID_ge)
        expr.make_bool(f0>=f1);
      else if(expr.id()==ID_le)
        expr.make_bool(f0<=f1);
      else if(expr.id()==ID_gt)
        expr.make_bool(f0>f1);
      else if(expr.id()==ID_lt)
        expr.make_bool(f0<f1);
      else
        assert(false);
    
      return false;
    }
    else if(tmp0.type().id()==ID_floatbv)
    {
      ieee_floatt f0(to_constant_expr(tmp0));
      ieee_floatt f1(to_constant_expr(tmp1));

      if(expr.id()==ID_notequal)
        expr.make_bool(f0!=f1);
      else if(expr.id()==ID_equal)
        expr.make_bool(f0==f1);
      else if(expr.id()==ID_ge)
        expr.make_bool(f0>=f1);
      else if(expr.id()==ID_le)
        expr.make_bool(f0<=f1);
      else if(expr.id()==ID_gt)
        expr.make_bool(f0>f1);
      else if(expr.id()==ID_lt)
        expr.make_bool(f0<f1);
      else
        assert(false);
    
      return false;
    }
    else if(tmp0.type().id()==ID_rational)
    {
      rationalt r0, r1;

      if(to_rational(tmp0, r0))
        return true;

      if(to_rational(tmp1, r1))
        return true;

      if(expr.id()==ID_notequal)
        expr.make_bool(r0!=r1);
      else if(expr.id()==ID_equal)
        expr.make_bool(r0==r1);
      else if(expr.id()==ID_ge)
        expr.make_bool(r0>=r1);
      else if(expr.id()==ID_le)
        expr.make_bool(r0<=r1);
      else if(expr.id()==ID_gt)
        expr.make_bool(r0>r1);
      else if(expr.id()==ID_lt)
        expr.make_bool(r0<r1);
      else
        assert(false);

      return false;
    }
    else
    {
      mp_integer v0, v1;
      
      if(to_integer(tmp0, v0))
        return true;

      if(to_integer(tmp1, v1))
        return true;
      
      if(expr.id()==ID_notequal)
        expr.make_bool(v0!=v1);
      else if(expr.id()==ID_equal)
        expr.make_bool(v0==v1);
      else if(expr.id()==ID_ge)
        expr.make_bool(v0>=v1);
      else if(expr.id()==ID_le)
        expr.make_bool(v0<=v1);
      else if(expr.id()==ID_gt)
        expr.make_bool(v0>v1);
      else if(expr.id()==ID_lt)
        expr.make_bool(v0<v1);
      else
        assert(false);

      return false;
    }
  }
  else if(op0_is_const)
  {
    // we want the constant on the RHS

    if(expr.id()==ID_ge)
      expr.id(ID_le);
    else if(expr.id()==ID_le)
      expr.id(ID_ge);
    else if(expr.id()==ID_gt)
      expr.id(ID_lt);
    else if(expr.id()==ID_lt)
      expr.id(ID_gt);
    
    expr.op0().swap(expr.op1());
    
    // one is constant
    simplify_inequality_constant(expr);
    return false;
  }
  else if(op1_is_const)
  {
    // one is constant
    return simplify_inequality_constant(expr); 
  }
  else
  {
    // both are not constant
    return simplify_inequality_not_constant(expr);
  }
    
  assert(false);
  return false;
}

/*******************************************************************\

Function: simplify_exprt::eliminate_common_addends

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::eliminate_common_addends(
  exprt &op0,
  exprt &op1)
{
  // we can't eliminate zeros
  if(op0.is_zero() ||
     op1.is_zero() ||
     (op0.is_constant() &&
      to_constant_expr(op0).get_value()==ID_NULL) ||
     (op1.is_constant() &&
      to_constant_expr(op1).get_value()==ID_NULL))
    return true;
  
  if(op0.id()==ID_plus)
  {
    bool result=true;

    Forall_operands(it, op0)
      if(!eliminate_common_addends(*it, op1))
        result=false;

    return result;
  }
  else if(op1.id()==ID_plus)
  {
    bool result=true;

    Forall_operands(it, op1)
      if(!eliminate_common_addends(op0, *it))
        result=false;
      
    return result;
  }
  else if(op0==op1)
  {
    if(!op0.is_zero() &&
       op0.type().id()!=ID_complex)
    {
      // elimination!
      op0=gen_zero(op0.type());
      op1=gen_zero(op1.type());
      return false;
    }
  }
  
  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_inequality_not_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_inequality_not_constant(exprt &expr)
{
  exprt::operandst &operands=expr.operands();
  
  // pretty much all of the simplifications below are unsound
  // for IEEE float because of NaN!
  
  if(ns.follow(expr.op0().type()).id()==ID_floatbv)
    return true;
  
  // eliminate strict inequalities
  if(expr.id()==ID_notequal)
  {
    expr.id(ID_equal);
    simplify_inequality_not_constant(expr);
    expr.make_not();
    simplify_node(expr);
    return false;
  }
  else if(expr.id()==ID_gt)
  {
    expr.id(ID_ge);
    // swap operands
    expr.op0().swap(expr.op1());
    simplify_inequality_not_constant(expr);
    expr.make_not();
    simplify_node(expr);
    return false;
  }
  else if(expr.id()==ID_lt)
  {
    expr.id(ID_ge);
    simplify_inequality_not_constant(expr);
    expr.make_not();
    simplify_node(expr);
    return false;
  }
  else if(expr.id()==ID_le)
  {
    expr.id(ID_ge);
    // swap operands
    expr.op0().swap(expr.op1());
    simplify_inequality_not_constant(expr);
    return false;
  }

  // now we only have >=, =

  assert(expr.id()==ID_ge || expr.id()==ID_equal);

  // syntactically equal?

  if(operands.front()==operands.back())
  {
    expr=true_exprt();
    return false;
  }

  // try constants

  value_listt values0, values1;

  bool ok0=!get_values(expr.op0(), values0);
  bool ok1=!get_values(expr.op1(), values1);

  if(ok0 && ok1)
  {
    bool first=true;
    bool result=false; // dummy initialization to prevent warning
    bool ok=true;

    // compare possible values

    forall_value_list(it0, values0)
      forall_value_list(it1, values1)
      {
        bool tmp;
        const mp_integer &int_value0=*it0;
        const mp_integer &int_value1=*it1;

        if(expr.id()==ID_ge)
          tmp=(int_value0 >= int_value1);
        else if(expr.id()==ID_equal)
          tmp=(int_value0 == int_value1);
        else
          assert(0);

        if(first)
        {
          result=tmp;
          first=false;
        }
        else if(result!=tmp)
        {
          ok=false;
          break;
        }
      }

    if(ok)
    {
      expr.make_bool(result);
      return false;
    }
  }
  
  // See if we can eliminate common addends on both sides.
  // On bit-vectors, this is only sound on '='.
  if(expr.id()==ID_equal)
  {
    if(!eliminate_common_addends(expr.op0(), expr.op1()))
    {
      // remove zeros
      simplify_node(expr.op0());
      simplify_node(expr.op1());
      simplify_inequality(expr); // recursive call
      return false;
    }
  }
  
  return true;
}  

/*******************************************************************\

Function: simplify_exprt::simplify_inequality_constant

  Inputs: an inequality with a constant on the RHS

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_inequality_constant(exprt &expr)
{
  // the constant is always on the RHS
  assert(expr.op1().is_constant());

  // do we deal with pointers?
  if(expr.op1().type().id()==ID_pointer)
  {
    if(expr.id()==ID_notequal)
    {
      expr.id(ID_equal);
      simplify_inequality_constant(expr);
      expr.make_not();
      simplify_node(expr);
      return false;
    }
  
    // very special case for pointers
    if(expr.id()==ID_equal &&
       expr.op1().is_constant() &&
       expr.op1().get(ID_value)==ID_NULL)
    {
      // the address of an object is never NULL
    
      if(expr.op0().id()==ID_address_of && 
         expr.op0().operands().size()==1)
      {
        if(expr.op0().op0().id()==ID_symbol ||
           expr.op0().op0().id()==ID_member ||
           expr.op0().op0().id()==ID_index)
        {
          expr=false_exprt();
          return false;
        }
      }
      else if(expr.op0().id()==ID_typecast &&
              expr.op0().operands().size()==1 &&
              expr.op0().type().id()==ID_pointer &&
              (expr.op0().op0().type().id()==ID_pointer ||
               config.ansi_c.NULL_is_zero))
      {
        // (type)ptr == NULL -> ptr == NULL
        // note that 'ptr' may be an integer
        exprt op=expr.op0().op0();
        expr.op0().swap(op);
        if(expr.op0().type().id()!=ID_pointer)
          expr.op1()=gen_zero(expr.op0().type());
        else
          expr.op1().type()=expr.op0().type();
        simplify_inequality(expr); // do again!
        return false;
      }
    }

    // all we are doing with pointers
    return true;
  }
  
  // is it a separation predicate?
  
  if(expr.op0().id()==ID_plus)
  {
    // see if there is a constant in the sum
    
    if(expr.id()==ID_equal || expr.id()==ID_notequal)
    {
      mp_integer constant=0;
      bool changed=false;
      
      Forall_operands(it, expr.op0())
      {
        if(it->is_constant())
        {
          mp_integer i;
          if(!to_integer(*it, i))
          {
            constant+=i;
            *it=gen_zero(it->type());
            changed=true;
          }
        }
      }
      
      if(changed)
      {
        // adjust constant
        mp_integer i;
        to_integer(expr.op1(), i);
        i-=constant;
        expr.op1()=from_integer(i, expr.op1().type());

        simplify_plus(expr.op0());
        simplify_inequality(expr);
        return false;
      }
    }
  }
  
  #if 1
  // (double)value REL const ---> value rel const
  // if 'const' can be represented exactly.
  
  if(expr.op0().id()==ID_typecast &&
     expr.op0().operands().size()==1 &&
     ns.follow(expr.op0().type()).id()==ID_floatbv &&
     ns.follow(expr.op0().op0().type()).id()==ID_floatbv)
  {
    ieee_floatt const_val(to_constant_expr(expr.op1()));
    ieee_floatt const_val_converted=const_val;
    const_val_converted.change_spec(to_floatbv_type(ns.follow(expr.op0().op0().type())));
    ieee_floatt const_val_converted_back=const_val_converted;
    const_val_converted_back.change_spec(to_floatbv_type(ns.follow(expr.op0().type())));
    if(const_val_converted_back==const_val)
    {
      exprt result=expr;
      result.op0()=expr.op0().op0();
      result.op1()=const_val_converted.to_expr();
      expr.swap(result);
      return false;
    }
  }
  #endif

  // is the constant zero?

  if(expr.op1().is_zero())
  {
    if(expr.id()==ID_ge &&
       expr.op0().type().id()==ID_unsignedbv)
    {
      // zero is always smaller or equal something unsigned
      expr=true_exprt();
      return false;
    }

    exprt &operand=expr.op0();

    if(expr.id()==ID_equal)
    {
      // rules below do not hold for >=
      if(operand.id()==ID_unary_minus)
      {
        if(operand.operands().size()!=1) return true;
        exprt tmp;
        tmp.swap(operand.op0());
        operand.swap(tmp);
        return false;
      }
      else if(operand.id()==ID_plus)
      {
        // simplify a+-b=0 to a=b

        if(operand.operands().size()==2)
        {
          // if we have -b+a=0, make that a+(-b)=0

          if(operand.op0().id()==ID_unary_minus)
            operand.op0().swap(operand.op1());

          if(operand.op1().id()==ID_unary_minus &&
             operand.op1().operands().size()==1)
          {
            exprt tmp(expr.id(), expr.type());
            tmp.operands().resize(2);
            tmp.op0().swap(operand.op0());
            tmp.op1().swap(operand.op1().op0());
            expr.swap(tmp);
            return false;
          }
        }
      }
    }
  }

  // are we comparing with a typecast from bool?
  if(expr.op0().id()==ID_typecast &&
     expr.op0().operands().size()==1 &&
     expr.op0().op0().type().id()==ID_bool)
  {
    // we re-write (TYPE)boolean == 0 -> !boolean
    if(expr.op1().is_zero() && expr.id()==ID_equal)
    {
      expr=expr.op0().op0();
      expr.make_not();
      return false;
    }

    // we re-write (TYPE)boolean != 0 -> boolean
    if(expr.op1().is_zero() && expr.id()==ID_notequal)
    {
      expr=expr.op0().op0();
      return false;
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_ieee_float_relation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_ieee_float_relation(exprt &expr)
{
  assert(expr.id()==ID_ieee_float_equal ||
         expr.id()==ID_ieee_float_notequal);

  exprt::operandst &operands=expr.operands();

  if(expr.type().id()!=ID_bool) return true;

  if(operands.size()!=2) return true;

  // types must match
  if(expr.op0().type()!=expr.op1().type())
    return true;

  if(expr.op0().type().id()!=ID_floatbv)
    return true;

  // first see if we compare to a constant

  if(expr.op0().is_constant() &&
     expr.op1().is_constant())
  {
    ieee_floatt f0(to_constant_expr(expr.op0()));
    ieee_floatt f1(to_constant_expr(expr.op1()));

    if(expr.id()==ID_ieee_float_notequal)
      expr.make_bool(ieee_not_equal(f0, f1));
    else if(expr.id()==ID_ieee_float_equal)
      expr.make_bool(ieee_equal(f0, f1));
    else
      assert(false);
  
    return false;
  }

  if(expr.op0()==expr.op1())
  {
    // x!=x is the same as saying isnan(op)
    exprt isnan(ID_isnan, bool_typet());
    isnan.copy_to_operands(expr.op0());

    if(expr.id()==ID_ieee_float_notequal)
    {
    }
    else if(expr.id()==ID_ieee_float_equal)
      isnan.make_not();
    else
      assert(false);
  
    expr.swap(isnan);
    return false;
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_lambda

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_lambda(exprt &expr)
{
  bool result=true;

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_with

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_with(exprt &expr)
{
  bool result=true;
  
  if((expr.operands().size()%2)!=1)
    return true;
    
  const typet op0_type=ns.follow(expr.op0().type());

  // now look at first operand
  
  if(op0_type.id()==ID_struct)
  {
    if(expr.op0().id()==ID_struct ||
       expr.op0().id()==ID_constant)
    {
      while(expr.operands().size()>1)
      {
        const irep_idt &component_name=
          expr.op1().get(ID_component_name);

        if(!to_struct_type(op0_type).
           has_component(component_name))
          return result;

        unsigned number=to_struct_type(op0_type).
           component_number(component_name);

        expr.op0().operands()[number].swap(expr.op2());

        expr.operands().erase(++expr.operands().begin());
        expr.operands().erase(++expr.operands().begin());

        result=false;
      }
    }
  }
  else if(expr.op0().type().id()==ID_array)
  {
    if(expr.op0().id()==ID_array ||
       expr.op0().id()==ID_constant)
    {
      while(expr.operands().size()>1)
      {
        mp_integer i;
        
        if(to_integer(expr.op1(), i))
          break;
          
        if(i<0 || i>=expr.op0().operands().size())
          break;
          
        if(!expr.op2().is_constant())
          break;

        expr.op0().operands()[integer2long(i)].swap(expr.op2());

        expr.operands().erase(++expr.operands().begin());
        expr.operands().erase(++expr.operands().begin());

        result=false;
      }
    }
  }

  if(expr.operands().size()==1)
  {
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
    result=false;
  }

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_update

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_update(exprt &expr)
{
  if(expr.operands().size()!=3)
    return true;

  // this is to push updates into (possibly nested) constants
  
  const exprt::operandst &designator=to_update_expr(expr).designator();
  
  exprt updated_value=to_update_expr(expr).old();
  exprt *value_ptr=&updated_value;

  for(exprt::operandst::const_iterator
      it=designator.begin();
      it!=designator.end();
      it++)
  {
    const typet &value_ptr_type=ns.follow(value_ptr->type());
    
    if(it->id()==ID_index_designator &&
       value_ptr->id()==ID_array)
    {
      mp_integer i;
      
      if(to_integer(it->op0(), i))
        return true;
        
      if(i<0 || i>=value_ptr->operands().size())
        return true;

      value_ptr=&value_ptr->operands()[integer2long(i)];
    }
    else if(it->id()==ID_member_designator &&
            value_ptr->id()==ID_struct)
    {
      const irep_idt &component_name=
        it->get(ID_component_name);
        
      if(!to_struct_type(value_ptr_type).
         has_component(component_name))
        return true;

      unsigned number=to_struct_type(value_ptr_type).
        component_number(component_name);
        
      assert(number<value_ptr->operands().size());

      value_ptr=&value_ptr->operands()[number];
    }
    else
      return true; // give up, unkown designator
  }

  // found, done
  *value_ptr=to_update_expr(expr).new_value();
  expr.swap(updated_value);

  return false;
}

/*******************************************************************\

Function: simplify_exprt::simplify_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_index(exprt &expr)
{
  bool result=true;

  // extra arithmetic optimizations
  const exprt &index=to_index_expr(expr).index();
  const exprt &array=to_index_expr(expr).array();

  if(index.id()==ID_div &&
     index.operands().size()==2)
  {
    if(index.op0().id()==ID_mult &&
       index.op0().operands().size()==2 &&
       index.op0().op1()==index.op1())
    {
      exprt tmp=index.op0().op0();
      expr.op1()=tmp;
      result=false;
    }
    else if(index.op0().id()==ID_mult &&
            index.op0().operands().size()==2 &&
            index.op0().op0()==index.op1())
    {
      exprt tmp=index.op0().op1();
      expr.op1()=tmp;
      result=false;
    }
  }

  if(array.id()==ID_lambda)
  {
    // simplify (lambda i: e)(x) to e[i/x]

    const exprt &lambda_expr=array;

    if(lambda_expr.operands().size()!=2) return true;

    if(expr.op1().type()==lambda_expr.op0().type())
    {
      exprt tmp=lambda_expr.op1();
      replace_expr(lambda_expr.op0(), expr.op1(), tmp);
      expr.swap(tmp);
      return false;
    }
  }
  else if(array.id()==ID_with)
  {
    // we have (a WITH [i:=e])[j]
  
    const exprt &with_expr=array;

    if(with_expr.operands().size()!=3) return true;
    
    if(with_expr.op1()==expr.op1())
    {
      // simplify (e with [i:=v])[i] to v
      exprt tmp=with_expr.op2();
      expr.swap(tmp);
      return false;
    }
    else
    {
      // Turn (a with i:=x)[j] into (i==j)?x:a[j].
      // watch out that the type of i and j might be different.
      equal_exprt equality_expr(expr.op1(), with_expr.op1());
      
      if(equality_expr.lhs().type()!=equality_expr.rhs().type())
        equality_expr.rhs().make_typecast(equality_expr.lhs().type());

      simplify_inequality(equality_expr);
      
      index_exprt new_index_expr;
      new_index_expr.type()=expr.type();
      new_index_expr.array()=with_expr.op0();
      new_index_expr.index()=expr.op1();

      simplify_index(new_index_expr); // recursive call

      exprt if_expr(ID_if, expr.type());
      if_expr.reserve_operands(3);
      if_expr.move_to_operands(equality_expr);
      if_expr.copy_to_operands(with_expr.op2());
      if_expr.move_to_operands(new_index_expr);

      simplify_if(if_expr);

      expr.swap(if_expr);

      return false;
    }
  }
  else if(array.id()==ID_constant ||
          array.id()==ID_array)
  {
    mp_integer i;
    
    if(to_integer(expr.op1(), i))
    {
    }
    else if(i<0 || i>=array.operands().size())
    {
      // out of bounds
    }
    else
    {
      // ok
      exprt tmp=array.operands()[integer2long(i)];
      expr.swap(tmp);
      return false;
    }
  }
  else if(array.id()==ID_string_constant)
  {
    mp_integer i;
    
    const irep_idt &value=array.get(ID_value);
  
    if(to_integer(expr.op1(), i))
    {
    }
    else if(i<0 || i>value.size())
    {
      // out of bounds
    }
    else
    {
      // terminating zero?
      char v=(i==value.size())?0:value[integer2long(i)];
      exprt tmp=from_integer(v, expr.type());
      expr.swap(tmp);
      return false;
    }
  }
  else if(array.id()==ID_array_of)
  {
    if(array.operands().size()==1)
    {
      exprt tmp=array.op0();
      expr.swap(tmp);
      return false;
    }
  }
  else if(array.id()=="array-list")
  {
    // These are index/value pairs, alternating.
    for(size_t i=0; i<array.operands().size()/2; i++)
    {
      exprt tmp_index=array.operands()[i*2];
      tmp_index.make_typecast(index.type());
      simplify(tmp_index);
      if(tmp_index==index)
      {
        exprt tmp=array.operands()[i*2+1];
        expr.swap(tmp);
        return false;
      }
    }
  }
  else if(array.id()==ID_byte_extract_little_endian ||
          array.id()==ID_byte_extract_big_endian)
  {
    const typet &array_type=ns.follow(array.type());

    if(array_type.id()==ID_array)
    {
      // This rewrites byte_extract(s, o, array_type)[i]
      // to byte_extract(s, o+offset, sub_type)

      mp_integer sub_size=pointer_offset_size(array_type.subtype(), ns);
      if(sub_size==-1) return true;

      // add offset to index
      mult_exprt offset(from_integer(sub_size, array.op1().type()), index);
      plus_exprt final_offset(array.op1(), offset);
      simplify_node(final_offset);

      exprt result(array.id(), expr.type());
      result.copy_to_operands(array.op0(), final_offset);
      expr.swap(result);

      simplify_rec(expr);

      return false;
    }
  }

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_object(exprt &expr)
{
  if(expr.id()==ID_plus)
  {
    if(expr.type().id()==ID_pointer)
    {
      // kill integers from sum
      Forall_operands(it, expr)
        if(ns.follow(it->type()).id()==ID_pointer)
        {
          exprt tmp=*it;
          expr.swap(tmp);
          simplify_object(expr);
          return false;
        }
    }
  }
  else if(expr.id()==ID_typecast)
  {
    const typet &op_type=ns.follow(expr.op0().type());
  
    assert(expr.operands().size()==1);
    
    if(op_type.id()==ID_pointer)
    {
      // cast from pointer to pointer
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
      simplify_object(expr);
      return false;
    }
    else if(op_type.id()==ID_signedbv || op_type.id()==ID_unsignedbv)
    {
      // cast from integer to pointer

      // We do a bit of special treatment for (TYPE *)(a+(int)&o),
      // which is re-written to '&o'.

      exprt tmp=expr.op0();
      if(tmp.id()==ID_plus && tmp.operands().size()==2)
      {
        if(tmp.op0().id()==ID_typecast &&
           tmp.op0().operands().size()==1 &&
           tmp.op0().op0().id()==ID_address_of)
        {
          expr=tmp.op0().op0();
          return false;
        }
        else if(tmp.op1().id()==ID_typecast &&
                tmp.op1().operands().size()==1 &&
                tmp.op1().op0().id()==ID_address_of)
        {
          expr=tmp.op1().op0();
          return false;
        }
      }
    }
  }
  else if(expr.id()==ID_address_of)
  {
    if(expr.operands().size()==1)
    {
      if(expr.op0().id()==ID_index && expr.op0().operands().size()==2)
      {
        // &some[i] -> &some
        address_of_exprt new_expr(expr.op0().op0());
        expr.swap(new_expr);
        simplify_object(expr); // recursion
        return false;
      }
      else if(expr.op0().id()==ID_member && expr.op0().operands().size()==1)
      {
        // &some.f -> &some
        address_of_exprt new_expr(expr.op0().op0());
        expr.swap(new_expr);
        simplify_object(expr); // recursion
        return false;
      }
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_pointer_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_pointer_object(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
  
  exprt &op=expr.op0();
  
  return simplify_object(op);
}

/*******************************************************************\

Function: simplify_exprt::simplify_dynamic_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_dynamic_object(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
  
  exprt &op=expr.op0();
  
  bool result=true;
  
  if(!simplify_object(op)) result=false;

  // NULL is not dynamic
  if(op.id()==ID_constant && op.get(ID_value)==ID_NULL)
  {
    expr=false_exprt();
    return false;
  }  

  // &something depends on the something
  if(op.id()==ID_address_of && op.operands().size()==1)
  {
    if(op.op0().id()==ID_symbol)
    {
      const irep_idt identifier=to_symbol_expr(op.op0()).get_identifier();

      // this is for the benefit of symex
      expr.make_bool(has_prefix(id2string(identifier), "symex_dynamic::"));
      return false;
    }
    else if(op.op0().id()==ID_string_constant)
    {
      expr=false_exprt();
      return false;
    }
    else if(op.op0().id()==ID_array)
    {
      expr=false_exprt();
      return false;
    }
  }
  
  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_invalid_pointer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_invalid_pointer(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
  
  exprt &op=expr.op0();
  
  bool result=true;
  
  if(!simplify_object(op)) result=false;

  // NULL is not invalid
  if(op.id()==ID_constant && op.get(ID_value)==ID_NULL)
  {
    expr=false_exprt();
    return false;
  }  
  
  // &anything is not invalid
  if(op.id()==ID_address_of)
  {
    expr=false_exprt();
    return false;
  }  
  
  return result;
}

/*******************************************************************\

Function: simplify_exprt::objects_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt simplify_exprt::objects_equal(const exprt &a, const exprt &b)
{
  if(a==b) return tvt(true);

  if(a.id()==ID_address_of && b.id()==ID_address_of &&
     a.operands().size()==1 && b.operands().size()==1)
    return objects_equal_address_of(a.op0(), b.op0());

  if(a.id()==ID_constant && b.id()==ID_constant &&
     a.get(ID_value)==ID_NULL && b.get(ID_value)==ID_NULL)
    return tvt(true);

  if(a.id()==ID_constant && b.id()==ID_address_of &&
     a.get(ID_value)==ID_NULL)
    return tvt(false);

  if(b.id()==ID_constant && a.id()==ID_address_of &&
     b.get(ID_value)==ID_NULL)
    return tvt(false);

  return tvt(tvt::TV_UNKNOWN);
}

/*******************************************************************\

Function: simplify_exprt::objects_equal_address_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt simplify_exprt::objects_equal_address_of(const exprt &a, const exprt &b)
{
  if(a==b) return tvt(true);

  if(a.id()==ID_symbol && b.id()==ID_symbol)
  {
    if(a.get(ID_identifier)==b.get(ID_identifier))
      return tvt(true);
  }
  else if(a.id()==ID_index && b.id()==ID_index)
  {
    if(a.operands().size()==2 && b.operands().size()==2)
      return objects_equal_address_of(a.op0(), b.op0());
  }
  else if(a.id()==ID_member && b.id()==ID_member)
  {
    if(a.operands().size()==1 && b.operands().size()==1)
      return objects_equal_address_of(a.op0(), b.op0());
  }

  return tvt(tvt::TV_UNKNOWN);
}

/*******************************************************************\

Function: simplify_exprt::simplify_object_size

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_object_size(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
  
  exprt &op=expr.op0();
  
  bool result=true;
  
  if(!simplify_object(op)) result=false;
  
  if(op.id()==ID_address_of && op.operands().size()==1)
  {
    if(op.op0().id()==ID_symbol)
    {
      // just get the type
      const typet &type=ns.follow(op.op0().type());

      exprt size=size_of_expr(type, ns);

      if(size.is_not_nil())
      {
        typet type=expr.type();

        if(size.type()!=type)
        {
          size.make_typecast(type);
          simplify_node(size);
        }

        expr=size;
        return false;
      }
    }
    else if(op.op0().id()==ID_string_constant)
    {
      typet type=expr.type();
      expr=from_integer(op.op0().get(ID_value).size()+1, type);
      return false;
    }
  }
  
  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_good_pointer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_good_pointer(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
  
  // we expand the definition
  exprt def=good_pointer_def(expr.op0(), ns);

  // recursive call
  simplify_node(def);  
  
  expr.swap(def);

  return false;
}

/*******************************************************************\

Function: simplify_exprt::simplify_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_member(exprt &expr)
{
  if(expr.operands().size()!=1) return true;

  const irep_idt &component_name=
    to_member_expr(expr).get_component_name();

  exprt &op=expr.op0();
  const typet &op_type=ns.follow(op.type());

  if(op.id()==ID_with)
  {
    // the following optimization only works on structs,
    // and not on unions
  
    if(op.operands().size()>=3 &&
       op_type.id()==ID_struct)
    {
      exprt::operandst &operands=op.operands();

      while(operands.size()>1)
      {
        exprt &op1=operands[operands.size()-2];
        exprt &op2=operands[operands.size()-1];

        if(op1.get(ID_component_name)==component_name)
        {
          // found it!
          exprt tmp;
          tmp.swap(op2);
          expr.swap(tmp);

          // do this recursively
          simplify_rec(expr);

          return false;
        }
        else // something else, get rid of it
          operands.resize(operands.size()-2);
      }
      
      if(op.operands().size()==1)
      {
        exprt tmp;
        tmp.swap(op.op0());
        op.swap(tmp);
        // do this recursively
        simplify_member(expr);
      }

      return false;      
    }
    else if(op_type.id()==ID_union)
    {
      const with_exprt &with_expr=to_with_expr(op);

      if(with_expr.where().get(ID_component_name)==component_name)
      {
        // WITH(s, .m, v).m -> v
        expr=with_expr.new_value();

        // do this recursively
        simplify_rec(expr);

        return false;
      }
    }
  }
  else if(op.id()==ID_update)
  {
    if(op.operands().size()==3 &&
       op_type.id()==ID_struct)
    {
      const update_exprt &update_expr=to_update_expr(op);
      const exprt::operandst &designator=update_expr.designator();

      // look at very first designator
      if(designator.size()==1 &&
         designator.front().id()==ID_member_designator)
      {
        if(designator.front().get(ID_component_name)==component_name)
        {
          // UPDATE(s, .m, v).m -> v
          exprt tmp=update_expr.new_value();
          expr.swap(tmp);

          // do this recursively
          simplify_rec(expr);

          return false;
        }
        // the following optimization only works on structs,
        // and not on unions
        else if(op_type.id()==ID_struct)
        {
          // UPDATE(s, .m1, v).m2 -> s.m2
          exprt tmp=update_expr.old();
          op.swap(tmp);

          // do this recursively
          simplify_rec(expr);

          return false;
        }
      }
    }
  }
  else if(op.id()==ID_struct ||
          op.id()==ID_constant)
  {
    if(op_type.id()==ID_struct)
    {
      // pull out the right member
      const struct_typet &struct_type=to_struct_type(op_type);
      if(struct_type.has_component(component_name))
      {
        unsigned number=struct_type.component_number(component_name);
        exprt tmp;
        tmp.swap(op.operands()[number]);
        expr.swap(tmp);
        return false;
      }
    }
  }
  else if(op.id()==ID_byte_extract_little_endian ||
          op.id()==ID_byte_extract_big_endian)
  {
    if(op_type.id()==ID_struct)
    {
      // This rewrites byte_extract(s, o, struct_type).member
      // to byte_extract(s, o+member_offset, member_type)
    
      const struct_typet &struct_type=to_struct_type(op_type);
      const struct_typet::componentt &component=
        struct_type.get_component(component_name);

      if(component.is_nil() || component.type().id()==ID_c_bit_field)
        return true;

      // add member offset to index
      mp_integer offset_int=member_offset(struct_type, component_name, ns);
      if(offset_int==-1) return true;
 
      const exprt &struct_offset=op.op1();
      exprt member_offset=from_integer(offset_int, struct_offset.type());
      plus_exprt final_offset(struct_offset, member_offset);
      simplify_node(final_offset);

      exprt result(op.id(), expr.type());
      result.copy_to_operands(op.op0(), final_offset);
      expr.swap(result);

      simplify_rec(expr);

      return false;
    }
  }
  else if(op.id()==ID_union && op_type.id()==ID_union)
  {
    // trivial?
    if(ns.follow(to_union_expr(op).op().type())==ns.follow(expr.type()))
    {
      exprt tmp=to_union_expr(op).op();
      expr.swap(tmp);
      return false;
    }
    
    // need to convert!
    mp_integer target_size=
      pointer_offset_size(expr.type(), ns);

    if(target_size!=-1)
    {
      mp_integer target_bits=target_size*8;
      std::string bits=expr2bits(op);
      
      // TODO: we effectively do little-endian here

      if(mp_integer(bits.size())>=target_bits)
      {
        std::string bits_cut=std::string(bits, 0, integer2long(target_bits));
      
        exprt tmp=bits2expr(bits_cut, expr.type());

        if(tmp.is_not_nil())
        {
          expr=tmp;
          return false;
        }
      }
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::bits2expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt simplify_exprt::bits2expr(
  const std::string &bits,
  const typet &_type)
{
  const typet &type=ns.follow(_type);

  if(type.id()==ID_unsignedbv ||
     type.id()==ID_signedbv ||
     type.id()==ID_floatbv ||
     type.id()==ID_fixedbv)
  {
    unsigned width=to_bitvector_type(type).get_width();
    if(bits.size()==width)
      return constant_exprt(bits, type);
  }
  else if(type.id()==ID_c_enum)
  {
    unsigned width=to_bitvector_type(type.subtype()).get_width();
    if(bits.size()==width)
      return constant_exprt(bits, type);
  }
  else if(type.id()==ID_c_enum_tag)
    return
      bits2expr(
        bits,
        ns.follow_tag(to_c_enum_tag_type(type)));
  else if(type.id()==ID_union)
  {
    // need to find full-size member
  }
  else if(type.id()==ID_struct)
  {
    // need to split up; this exposes endianness
  }
  else if(type.id()==ID_array)
  {
    // need to split up; this exposes endianness
  }
  
  return nil_exprt();
}

/*******************************************************************\

Function: simplify_exprt::expr2bits

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string simplify_exprt::expr2bits(const exprt &expr)
{
  const typet &type=ns.follow(expr.type());

  if(expr.id()==ID_constant)
  {
    if(type.id()==ID_unsignedbv ||
       type.id()==ID_signedbv ||
       type.id()==ID_c_enum ||
       type.id()==ID_c_enum_tag ||
       type.id()==ID_floatbv ||
       type.id()==ID_fixedbv)
    {
      return id2string(to_constant_expr(expr).get_value());
    }
  }
  else if(expr.id()==ID_union)
  {
    return expr2bits(to_union_expr(expr).op());
  }
  else if(expr.id()==ID_struct)
  {
    std::string result;
    forall_operands(it, expr)
      result+=expr2bits(*it);
    return result;
  }
  else if(expr.id()==ID_array)
  {
    std::string result;
    forall_operands(it, expr)
      result+=expr2bits(*it);
    return result;
  }
  
  return "";
}

/*******************************************************************\

Function: simplify_exprt::simplify_byte_extract

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_byte_extract(exprt &expr)
{
  byte_extract_exprt &be=to_byte_extract_expr(expr);

  // don't do any of the following if endianness doesn't match, as
  // bytes need to be swapped
  if(byte_extract_id()!=expr.id())
    return true;

  // byte_extract(byte_update(root, offset, value), offset) =>
  // value
  if(((be.id()==ID_byte_extract_big_endian &&
       be.op().id()==ID_byte_update_big_endian) ||
      (be.id()==ID_byte_extract_little_endian &&
       be.op().id()==ID_byte_update_little_endian)) &&
     be.offset()==be.op().op1() &&
     base_type_eq(be.type(), be.op().op2().type(), ns))
  {
    expr=be.op().op2();
    return false;
  }
  
  // the following require a constant offset
  mp_integer offset;
  if(to_integer(be.offset(), offset) || offset<0)
    return true;

  // byte extract of full object is object
  if(offset==0 &&
     base_type_eq(expr.type(), be.op().type(), ns))
  {
    expr=be.op();

    return false;
  }

  const mp_integer el_size=pointer_offset_size(be.type(), ns);
  // no proper simplification for be.type()==void
  // or types of unknown size
  if(be.type().id()==ID_empty ||
     el_size<0)
    return true;

  // rethink the remaining code to correctly handle big endian
  if(expr.id()!=ID_byte_extract_little_endian) return true;
  
  // get type of object
  const typet &op_type=ns.follow(be.op().type());
  
  if(op_type.id()==ID_array)
  {
    exprt result=be.op();

    // try proper array or string constant
    for(const typet *op_type_ptr=&op_type;
        op_type_ptr->id()==ID_array;
        op_type_ptr=&(ns.follow(*op_type_ptr).subtype()))
    {
      // no arrays of zero-sized objects
      assert(el_size>0);

      if(base_type_eq(be.type(), op_type_ptr->subtype(), ns))
      {
        if(offset%el_size==0)
        {
          offset/=el_size;

          result=
            index_exprt(
              result,
              from_integer(offset, be.offset().type()));

          expr=result;

          return false;
        }
      }
      else
      {
        mp_integer sub_size=pointer_offset_size(op_type_ptr->subtype(), ns);

        if(sub_size>0)
        {
          mp_integer index=offset/sub_size;
          offset%=sub_size;

          result=
            index_exprt(
              result,
              from_integer(index, be.offset().type()));
        }
      }
    }
  }
  else if(op_type.id()==ID_struct)
  {
    const struct_typet &struct_type=
      to_struct_type(op_type);
    const struct_typet::componentst &components=
      struct_type.components();

    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        ++it)
    {
      mp_integer m_offset=
        member_offset(struct_type, it->get_name(), ns);
      mp_integer m_size=
        pointer_offset_size(it->type(), ns);
        
      if(offset==m_offset &&
         el_size==m_size &&
         base_type_eq(be.type(), it->type(), ns))
      {
        expr=member_exprt(be.op(), it->get_name(), it->type());
        simplify_rec(expr);
        return false;
      }
      else if(m_offset>=0 &&
              m_size>=0 &&
              offset>=m_offset &&
              offset+el_size<=m_offset+m_size)
      {
        be.op()=member_exprt(be.op(), it->get_name(), it->type());
        be.offset()=
          from_integer(offset-m_offset, be.offset().type());

        return false;
      }
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_byte_update

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_byte_update(exprt &expr)
{
  if(expr.operands().size()!=3) return true;
  
  byte_update_exprt &bu_expr=to_byte_update_expr(expr);

  // byte_update(byte_update(root, offset, value), offset, value2) =>
  // byte_update(root, offset, value2)
  if(bu_expr.id()==bu_expr.op().id() &&
     bu_expr.offset()==bu_expr.op().op1() &&
     base_type_eq(bu_expr.value().type(), bu_expr.op().op2().type(), ns))
  {
    bu_expr.op()=bu_expr.op().op0();
    return false;
  }

  /*
   * byte_update(root, offset, 
   *             extract(root, offset) WITH component:=value)
   * =>
   * byte_update(root, offset + component offset, 
   *             value)
   */

  if(bu_expr.id()!=ID_byte_update_little_endian) return true;

  exprt &root=bu_expr.op();
  exprt &offset=bu_expr.offset();
  const exprt &value=bu_expr.value();

  if(bu_expr.value().id()==ID_with) 
  {
    exprt &with=bu_expr.value();

    if(with.operands().size()!=3) return true;

    if(with.op0().id()==ID_byte_extract_little_endian)
    {
      exprt &extract=with.op0();

      /* the simplification can be used only if 
         root and offset of update and extract
         are the same */
      if(extract.operands().size() != 2) return true;
      if(!(root == extract.op0())) return true;
      if(!(offset == extract.op1())) return true;

      const typet& tp = ns.follow(with.type());
      if(tp.id()==ID_struct) 
      {
        const struct_typet &struct_type=to_struct_type(tp);
        const irep_idt &component_name=with.op1().get(ID_component_name);
        
        // is this a bit field?
        if(struct_type.get_component(component_name).type().id()==ID_c_bit_field)
        {
          // don't touch -- might not be byte-aligned
        }
        else
        {
          // new offset = offset + component offset
          mp_integer i = member_offset(struct_type, 
                                       component_name, ns);
          if(i != -1) 
          {
            exprt compo_offset = from_integer(i, offset.type());
            plus_exprt new_offset (offset, compo_offset);
            simplify_node (new_offset);
            exprt new_value(with.op2());
            expr.op1().swap(new_offset);
            expr.op2().swap(new_value);
            simplify_byte_update(expr); // do this recursively
            return false;
          }
        }
      }
      else if(tp.id()==ID_array)
      {
        mp_integer i = pointer_offset_size(tp.subtype(), ns);
        if(i != -1)
        {
          exprt& index = with.op1();
          mult_exprt index_offset(index, from_integer(i, index.type()));
          simplify_node (index_offset);

          // index_offset may need a typecast
          if(!base_type_eq(offset.type(), index.type(), ns)) 
          {
            typecast_exprt tmp(index_offset, offset.type());
            simplify_node(tmp);
            index_offset.swap(tmp);
          }

          plus_exprt new_offset (offset, index_offset);
          simplify_node(new_offset);
          exprt new_value(with.op2());
          expr.op1().swap(new_offset);
          expr.op2().swap(new_value);
          simplify_byte_update(expr); // do this recursively
          return false;
        }
      }
    }
  }
  
  // the following require a constant offset
  mp_integer offset_int;
  if(to_integer(offset, offset_int) || offset_int<0)
    return true;
  
  const typet &op_type=ns.follow(root.type());
  
  // search for updates of members, and replace by 'with'
  if(op_type.id()==ID_struct)
  {
    const struct_typet &struct_type=
      to_struct_type(op_type);
    const struct_typet::componentst &components=
      struct_type.components();
      
    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        ++it)
    {
      mp_integer m_offset=
        member_offset(struct_type, it->get_name(), ns);
        
      if(offset_int==m_offset &&
         base_type_eq(it->type(), value.type(), ns))
      {
        exprt member_name(ID_member_name);
        member_name.set(ID_component_name, it->get_name());
        expr=with_exprt(root, member_name, value);
        simplify_node(expr);
        return false;
      }
    }
  }

  return true;
}

/*******************************************************************\

Function: sort_and_join

  Inputs:

 Outputs:

 Purpose: produce canonical ordering for associative and commutative
          binary operators

\*******************************************************************/

// The entries
//  { ID_plus,   ID_floatbv  },
//  { ID_mult,   ID_floatbv  },
//  { ID_plus,   ID_pointer  },
// are deliberately missing, as FP-addition and multiplication
// aren't associative. Addition to pointers isn't really
// associative.

struct saj_tablet
{
  const irep_idt id;
  const irep_idt type_id;
} const saj_table[]=
{
  { ID_plus,   ID_integer    },
  { ID_plus,   ID_natural    },
  { ID_plus,   ID_real       },
  { ID_plus,   ID_complex    },
  { ID_plus,   ID_rational   },
  { ID_plus,   ID_unsignedbv },
  { ID_plus,   ID_signedbv   },
  { ID_plus,   ID_fixedbv    },
  { ID_mult,   ID_integer    },
  { ID_mult,   ID_natural    },
  { ID_mult,   ID_real       },
  { ID_mult,   ID_complex    },
  { ID_mult,   ID_rational   },
  { ID_mult,   ID_unsignedbv },
  { ID_mult,   ID_signedbv   },
  { ID_mult,   ID_fixedbv    },
  { ID_and,    ID_bool       },
  { ID_or,     ID_bool       },
  { ID_xor,    ID_bool       },
  { ID_bitand, ID_unsignedbv },
  { ID_bitand, ID_signedbv   },
  { ID_bitand, ID_floatbv    },
  { ID_bitand, ID_fixedbv    },
  { ID_bitor,  ID_unsignedbv },
  { ID_bitor,  ID_signedbv   },
  { ID_bitor,  ID_floatbv    },
  { ID_bitor,  ID_fixedbv    },
  { ID_bitxor, ID_unsignedbv },
  { ID_bitxor, ID_signedbv   },
  { ID_bitxor, ID_floatbv    },
  { ID_bitxor, ID_fixedbv    },
  { irep_idt(), irep_idt()   }
};

bool sort_and_join(const irep_idt &id, const irep_idt &type_id)
{
  for(unsigned i=0; saj_table[i].id!=irep_idt(); i++)
    if(id==saj_table[i].id &&
       type_id==saj_table[i].type_id)
      return true;

  return false;
}

/*******************************************************************\

Function: sort_and_join

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::sort_and_join(exprt &expr)
{
  bool result=true;

  if(!expr.has_operands()) return true;

  if(!::sort_and_join(expr.id(), expr.type().id()))
    return true;

  // check operand types

  forall_operands(it, expr)
    if(!::sort_and_join(expr.id(), it->type().id()))
      return true;

  // join expressions

  for(size_t i=0; i<expr.operands().size();)
  {
    if(expr.operands()[i].id()==expr.id())
    {
      size_t no_joined=expr.operands()[i].operands().size();

      expr.operands().insert(expr.operands().begin()+i+1,
        expr.operands()[i].operands().begin(), 
        expr.operands()[i].operands().end());

      expr.operands().erase(expr.operands().begin()+i);

      i+=no_joined;

      result=false;
    }
    else
      i++;
  }

  // sort it

  result=sort_operands(expr.operands()) && result;

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_extractbits

  Inputs:

 Outputs:

 Purpose: Simplifies extracting of bits from a constant. 

\*******************************************************************/

bool simplify_exprt::simplify_extractbits(exprt &expr)
{
  assert(expr.operands().size()==3);

  const typet &op0_type=expr.op0().type();

  if(!is_bitvector_type(op0_type) &&
     !is_bitvector_type(expr.type()))
    return true;

  if(expr.op0().is_constant())
  {
    unsigned width=to_bitvector_type(op0_type).get_width();
    mp_integer start, end;
    
    if(to_integer(expr.op1(), start))
      return true;

    if(to_integer(expr.op2(), end))
      return true;

    if(start<0 || start>=width ||
       end  <0 || end  >=width)
      return true;

    assert(start>=end); //is this always the case??

    const irep_idt &value=expr.op0().get(ID_value);

    if(value.size()!=width)
      return true;

    std::string svalue=id2string(value);

    std::string extracted_value=
      svalue.substr(width-integer2long(start)-1,
                    integer2long(start-end+1));
    
    exprt tmp(ID_constant, expr.type());
    tmp.set(ID_value, extracted_value);
    expr.swap(tmp);

    return false;
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_unary_plus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_unary_plus(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  // simply remove, this is always 'nop'
  expr=expr.op0();
  return false;
}

/*******************************************************************\

Function: simplify_exprt::simplify_unary_minus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_unary_minus(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  if(!is_number(expr.type()))
    return true;

  exprt &operand=expr.op0();

  if(expr.type()!=operand.type())
    return true;

  if(operand.id()==ID_unary_minus)
  {
    // cancel out "-(-x)" to "x"
    if(operand.operands().size()!=1)
      return true;

    if(!is_number(operand.op0().type()))
      return true;

    exprt tmp;
    tmp.swap(expr.op0().op0());
    expr.swap(tmp);
    return false;
  }
  else if(operand.id()==ID_constant)
  {
    const irep_idt &type_id=expr.type().id();

    if(type_id==ID_integer ||
       type_id==ID_signedbv ||
       type_id==ID_unsignedbv)
    {
      mp_integer int_value;

      if(to_integer(expr.op0(), int_value))
        return true;

      exprt tmp=from_integer(-int_value, expr.type());

      if(tmp.is_nil())
        return true;

      expr.swap(tmp);

      return false;
    }
    else if(type_id==ID_rational)
    {
      rationalt r;
      if(to_rational(expr.op0(), r))
        return true;

      expr=from_rational(-r);
      return false;
    }
    else if(type_id==ID_fixedbv)
    {
      fixedbvt f(to_constant_expr(expr.op0()));
      f.negate();
      expr=f.to_expr();
      return false;
    }
    else if(type_id==ID_floatbv)
    {
      ieee_floatt f(to_constant_expr(expr.op0()));
      f.negate();
      expr=f.to_expr();
      return false;
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_node

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_node(exprt &expr)
{
  if(!expr.has_operands()) return true;

  //#define DEBUGX

  #ifdef DEBUGX
  exprt old(expr);
  #endif

  bool result=true;

  result=sort_and_join(expr) && result;

  #if 1 // use jump table?
  if(expr.id()==ID_typecast)
    result=simplify_typecast(expr) && result;
  else if(expr.id()==ID_equal || expr.id()==ID_notequal ||
          expr.id()==ID_gt    || expr.id()==ID_lt ||
          expr.id()==ID_ge    || expr.id()==ID_le)
    result=simplify_inequality(expr) && result;
  else if(expr.id()==ID_if)
    result=simplify_if(expr) && result;
  else if(expr.id()==ID_lambda)
    result=simplify_lambda(expr) && result;
  else if(expr.id()==ID_with)
    result=simplify_with(expr) && result;
  else if(expr.id()==ID_update)
    result=simplify_update(expr) && result;
  else if(expr.id()==ID_index)
    result=simplify_index(expr) && result;
  else if(expr.id()==ID_member)
    result=simplify_member(expr) && result;
  else if(expr.id()==ID_byte_update_little_endian ||
          expr.id()==ID_byte_update_big_endian)
    result=simplify_byte_update(expr) && result;
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
    result=simplify_byte_extract(expr) && result;
  else if(expr.id()==ID_pointer_object)
    result=simplify_pointer_object(expr) && result;
  else if(expr.id()==ID_dynamic_object)
    result=simplify_dynamic_object(expr) && result;
  else if(expr.id()==ID_invalid_pointer)
    result=simplify_invalid_pointer(expr) && result;
  else if(expr.id()==ID_object_size)
    result=simplify_object_size(expr) && result;
  else if(expr.id()==ID_good_pointer)
    result=simplify_good_pointer(expr) && result;
  else if(expr.id()==ID_div)
    result=simplify_div(expr) && result;
  else if(expr.id()==ID_mod)
    result=simplify_mod(expr) && result;
  else if(expr.id()==ID_bitnot)
    result=simplify_bitnot(expr) && result;
  else if(expr.id()==ID_bitnot ||
          expr.id()==ID_bitand ||
          expr.id()==ID_bitor ||
          expr.id()==ID_bitxor)
    result=simplify_bitwise(expr) && result;
  else if(expr.id()==ID_ashr || expr.id()==ID_lshr || expr.id()==ID_shl)
    result=simplify_shifts(expr) && result;
  else if(expr.id()==ID_plus)
    result=simplify_plus(expr) && result;
  else if(expr.id()==ID_minus)
    result=simplify_minus(expr) && result;
  else if(expr.id()==ID_mult)
    result=simplify_mult(expr) && result;
  else if(expr.id()==ID_floatbv_plus ||
          expr.id()==ID_floatbv_minus ||
          expr.id()==ID_floatbv_mult ||
          expr.id()==ID_floatbv_div)
    result=simplify_floatbv_op(expr) && result;
  else if(expr.id()==ID_floatbv_typecast)
    result=simplify_floatbv_typecast(expr) && result;
  else if(expr.id()==ID_unary_minus)
    result=simplify_unary_minus(expr) && result;
  else if(expr.id()==ID_unary_plus)
    result=simplify_unary_plus(expr) && result;
  else if(expr.id()==ID_not)
    result=simplify_not(expr) && result;
  else if(expr.id()==ID_implies || expr.id()==ID_iff ||
          expr.id()==ID_or      || expr.id()==ID_xor ||
          expr.id()==ID_and)
    result=simplify_boolean(expr) && result;
  else if(expr.id()==ID_dereference)
    result=simplify_dereference(expr) && result;
  else if(expr.id()==ID_address_of)
    result=simplify_address_of(expr) && result;
  else if(expr.id()==ID_pointer_offset)
    result=simplify_pointer_offset(expr) && result;
  else if(expr.id()==ID_extractbit)
    result=simplify_extractbit(expr) && result;
  else if(expr.id()==ID_concatenation)
    result=simplify_concatenation(expr) && result;
  else if(expr.id()==ID_extractbits) 
    result=simplify_extractbits(expr) && result;
  else if(expr.id()==ID_ieee_float_equal ||
          expr.id()==ID_ieee_float_notequal)
    result=simplify_ieee_float_relation(expr) && result;
  else if(expr.id()==ID_isinf)
    result=simplify_isinf(expr) && result;
  else if(expr.id()==ID_isnan)
    result=simplify_isnan(expr) && result;
  else if(expr.id()==ID_isnormal)
    result=simplify_isnormal(expr) && result;
  else if(expr.id()==ID_abs)
    result=simplify_abs(expr) && result;
  else if(expr.id()==ID_sign)
    result=simplify_sign(expr) && result;
  #else
  
  unsigned no=expr.id().get_no();
  
  if(no<simplify_jump_table.size())
  {
    jump_table_entryt entry=simplify_jump_table[no];
    if(entry!=NULL)
      result=(this->*entry)(expr) && result;
  }
  
  #endif

  #ifdef DEBUGX
  if(!result)
  {
    std::cout << "===== " << from_expr(ns, "", old)
              << "\n ---> " << from_expr(ns, "", expr)
              << "\n";
  }
  #endif

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_rec

  Inputs:

 Outputs: returns true if expression unchanged;
          returns false if changed

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_rec(exprt &expr)
{
  // look up in cache
  
  #ifdef USE_CACHE
  std::pair<simplify_expr_cachet::containert::iterator, bool>
    cache_result=simplify_expr_cache.container().
      insert(std::pair<exprt, exprt>(expr, exprt()));
  
  if(!cache_result.second) // found!
  {
    const exprt &new_expr=cache_result.first->second;
  
    if(new_expr.id()==irep_idt())
      return true; // no change
    
    expr=new_expr;
    return false;
  }
  #endif

  // We work on a copy to prevent unnecessary destruction of sharing.
  exprt tmp=expr;
  bool result=true;
  
  if(tmp.has_operands())
  {
    if(tmp.id()==ID_address_of)
    {
      // the argument of this expression needs special treatment
    }
    else
    {
      Forall_operands(it, tmp)
        if(!simplify_rec(*it)) // recursive call
          result=false;
    }
  }

  if(!simplify_node(tmp)) result=false;

  if(!result)
  {
    expr.swap(tmp);
  
    #ifdef USE_CACHE
    // save in cache
    cache_result.first->second=expr;
    #endif
  }

  return result;
}

/*******************************************************************\

Function: simplify

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify(exprt &expr, const namespacet &ns)
{
  return simplify_exprt(ns).simplify(expr);
}

/*******************************************************************\

Function: simplify_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt simplify_expr(const exprt &src, const namespacet &ns)
{
  exprt tmp=src;
  simplify_exprt(ns).simplify(tmp);
  return tmp;
}

