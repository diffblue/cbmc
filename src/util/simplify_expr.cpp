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
#include "expr_util.h"
#include "std_expr.h"
#include "fixedbv.h"
#include "pointer_offset_size.h"
#include "rational_tools.h"
#include "config.h"
#include "base_type.h"
#include "namespace.h"
#include "threeval.h"
#include "pointer_predicates.h"
#include "prefix.h"
#include "byte_operators.h"
#include "bv_arithmetic.h"
#include "endianness_map.h"
#include "simplify_utils.h"

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

Function: simplify_exprt::simplify_popcount

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_popcount(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
 
  if(expr.op0().is_constant())
  {
    const typet &type=ns.follow(expr.op0().type());
    
    if(type.id()==ID_signedbv ||
       type.id()==ID_unsignedbv)
    {
      mp_integer value;
      if(!to_integer(expr.op0(), value))
      {
        unsigned result;
        
        for(result=0; value!=0; value=value>>1)
          if(value.is_odd()) result++;
        
        expr=from_integer(result, expr.type());
        
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
     (to_constant_expr(expr.op0()).get_value()==ID_NULL ||
      (expr.op0().is_zero() && config.ansi_c.NULL_is_zero)))
  {
    exprt tmp=expr.op0();
    tmp.type()=expr.type();
    to_constant_expr(tmp).set_value(ID_NULL);
    tmp.remove(ID_C_cformat);
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

  // mildly more elaborate version of the above:
  // (int)((T*)0 + int) -> (int)(sizeof(T)*(size_t)int) if NULL is zero
  if(config.ansi_c.NULL_is_zero &&
     (expr_type.id()==ID_signedbv || expr_type.id()==ID_unsignedbv) &&
     expr.op0().id()==ID_plus &&
     expr.op0().operands().size()==2 &&
     expr.op0().op0().id()==ID_typecast &&
     expr.op0().op0().operands().size()==1 &&
     expr.op0().op0().op0().is_zero() &&
     op_type.id()==ID_pointer)
  {
    unsignedbv_typet size_type(config.ansi_c.pointer_width);

    mp_integer sub_size=pointer_offset_size(op_type.subtype(), ns);
    if(sub_size!=-1)
    {
      // void*
      if(sub_size==0 || sub_size==1)
        expr.op0()=typecast_exprt(expr.op0().op1(), size_type);
      else
        expr.op0()=mult_exprt(from_integer(sub_size, size_type),
                              typecast_exprt(expr.op0().op1(), size_type));

      simplify_rec(expr.op0());
      simplify_typecast(expr); // rec. call
      return false;
    }
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
       to_bitvector_type(expr_type).get_width()<=
         to_bitvector_type(operand.type()).get_width())
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

      // We do a bit of special treatment for (TYPE *)(a+(int)&o) and
      // (TYPE *)(a+(int)((T*)&o+x)), which are re-written to '&o'.

      exprt tmp=expr.op0();
      if(tmp.id()==ID_plus && tmp.operands().size()==2)
      {
        exprt cand=tmp.op0().id()==ID_typecast?tmp.op0():tmp.op1();

        if(cand.id()==ID_typecast &&
           cand.operands().size()==1 &&
           cand.op0().id()==ID_address_of)
        {
          expr=cand.op0();
          return false;
        }
        else if(cand.id()==ID_typecast &&
                cand.operands().size()==1 &&
                cand.op0().id()==ID_plus &&
                cand.op0().operands().size()==2 &&
                cand.op0().op0().id()==ID_typecast &&
                cand.op0().op0().operands().size()==1 &&
                cand.op0().op0().op0().id()==ID_address_of)
        {
          expr=cand.op0().op0().op0();
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

Function: simplify_exprt::bits2expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt simplify_exprt::bits2expr(
  const std::string &bits,
  const typet &_type,
  bool little_endian)
{
  // bits start at lowest memory address
  const typet &type=ns.follow(_type);

  if(type.id()==ID_unsignedbv ||
     type.id()==ID_signedbv ||
     type.id()==ID_floatbv ||
     type.id()==ID_fixedbv)
  {
    unsigned width=to_bitvector_type(type).get_width();
    if(bits.size()==width)
    {
      endianness_mapt map(type, little_endian, ns);

      std::string tmp=bits;
      for(std::string::size_type i=0; i<bits.size(); ++i)
        tmp[i]=bits[map.map_bit(i)];

      std::reverse(tmp.begin(), tmp.end());
      return constant_exprt(tmp, type);
    }
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
        ns.follow_tag(to_c_enum_tag_type(type)),
        little_endian);
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

std::string simplify_exprt::expr2bits(
  const exprt &expr,
  bool little_endian)
{
  // extract bits from lowest to highest memory address
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
      std::string nat=id2string(to_constant_expr(expr).get_value());
      std::reverse(nat.begin(), nat.end());

      endianness_mapt map(type, little_endian, ns);

      std::string result=nat;
      for(std::string::size_type i=0; i<nat.size(); ++i)
        result[map.map_bit(i)]=nat[i];

      return result;
    }
  }
  else if(expr.id()==ID_union)
  {
    return expr2bits(to_union_expr(expr).op(), little_endian);
  }
  else if(expr.id()==ID_struct)
  {
    std::string result;
    forall_operands(it, expr)
    {
      std::string tmp=expr2bits(*it, little_endian);
      if(tmp.empty()) return tmp; // failed
      result+=tmp;
    }
    return result;
  }
  else if(expr.id()==ID_array)
  {
    std::string result;
    forall_operands(it, expr)
    {
      std::string tmp=expr2bits(*it, little_endian);
      if(tmp.empty()) return tmp; // failed
      result+=tmp;
    }
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
          simplify_rec(expr);
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

Function: simplify_exprt::simplify_node_preorder

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_node_preorder(exprt &expr)
{
  bool result=true;

  #if __cplusplus > 199711L
  switch(expr.id())
  {
    case ID_address_of:
      // the argument of this expression needs special treatment
      break;

    default:
      if(expr.has_operands())
      {
        Forall_operands(it, expr)
          if(!simplify_rec(*it)) // recursive call
            result=false;
      }
  }
  #else
  if(expr.id()==ID_address_of)
  {
  }
  else if(expr.has_operands())
  {
    Forall_operands(it, expr)
      if(!simplify_rec(*it)) // recursive call
        result=false;
  }
  #endif

  return result;
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
  else if(expr.id()==ID_popcount)
    result=simplify_popcount(expr) && result;
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

  result=simplify_node_preorder(tmp);

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

