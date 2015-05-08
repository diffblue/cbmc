/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "expr_util.h"
#include "expr.h"
#include "fixedbv.h"
#include "ieee_float.h"
#include "std_expr.h"
#include "symbol.h"
#include "namespace.h"
#include "arith_tools.h"

/*******************************************************************\

Function: gen_zero

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt gen_zero(const typet &type)
{
  const irep_idt type_id=type.id();

  if(type_id==ID_rational ||
     type_id==ID_real ||
     type_id==ID_integer ||
     type_id==ID_natural)
  {
    return constant_exprt(ID_0, type);
  }
  else if(type_id==ID_c_enum)
  {
    exprt tmp=gen_zero(type.subtype());
    tmp.type()=type;
    return tmp;
  }
  else if(type_id==ID_c_enum_tag)
  {
    // Ha! We generate a typecast.
    exprt tmp=gen_zero(unsignedbv_typet(1));
    return typecast_exprt(tmp, type);
  }
  else if(type_id==ID_unsignedbv ||
          type_id==ID_signedbv ||
          type_id==ID_verilogbv ||
          type_id==ID_floatbv ||
          type_id==ID_fixedbv ||
          type_id==ID_c_bit_field ||
          type_id==ID_c_bool)
  {
    std::string value;
    unsigned width=to_bitvector_type(type).get_width();

    for(unsigned i=0; i<width; i++)
      value+='0';

    return constant_exprt(value, type);
  }
  else if(type_id==ID_complex)
  {
    exprt sub_zero=gen_zero(type.subtype());
    return complex_exprt(sub_zero, sub_zero, to_complex_type(type));
  }
  else if(type_id==ID_bool)
  {
    return false_exprt();
  }
  else if(type_id==ID_pointer)
  {
    return constant_exprt(ID_NULL, type);
  }
  else if(type_id==ID_vector &&
          to_vector_type(type).size().id()==ID_constant)
  {
    exprt sub_zero=gen_zero(type.subtype());
    mp_integer s;

    if(sub_zero.is_nil() ||
       to_integer(to_vector_type(type).size(), s))
      return sub_zero;

    exprt::operandst ops(integer2unsigned(s), sub_zero);
    vector_exprt v(to_vector_type(type));
    v.operands().swap(ops);

    return v;
  }
  else
    return nil_exprt();
}

/*******************************************************************\

Function: gen_one

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt gen_one(const typet &type)
{
  const irep_idt type_id=type.id();

  if(type_id==ID_bool)
    return true_exprt();
  else if(type_id==ID_rational ||
          type_id==ID_real ||
          type_id==ID_integer ||
          type_id==ID_natural)
  {
    return constant_exprt(ID_1, type);
  }
  else if(type_id==ID_unsignedbv ||
          type_id==ID_signedbv ||
          type_id==ID_c_bit_field ||
          type_id==ID_c_bool)
  {
    std::string value;
    unsigned width=to_bitvector_type(type).get_width();
    
    if(width!=0)
    {
      value.reserve(width);
      for(unsigned i=0; i<width-1; i++)
        value+='0';
      value+='1';
    }

    return constant_exprt(value, type);
  }
  else if(type_id==ID_c_enum)
  {
    exprt tmp=gen_one(type.subtype());
    tmp.type()=type;
    return tmp;
  }
  else if(type_id==ID_c_enum_tag)
  {
    // Ha! We generate a typecast.
    exprt tmp=gen_one(unsignedbv_typet(1));
    return typecast_exprt(tmp, type);
  }
  else if(type_id==ID_fixedbv)
  {
    fixedbvt fixedbv;
    fixedbv.spec=to_fixedbv_type(type);
    fixedbv.from_integer(1);
    return fixedbv.to_expr();
  }
  else if(type_id==ID_floatbv)
  {
    ieee_floatt ieee_float;
    ieee_float.spec=to_floatbv_type(type);
    ieee_float.from_integer(1);
    return ieee_float.to_expr();
  }
  else if(type_id==ID_complex)
  {
    exprt real=gen_one(type.subtype());
    exprt imag=gen_zero(type.subtype());
    return complex_exprt(real, imag, to_complex_type(type));
  }
  else if(type_id==ID_vector &&
          to_vector_type(type).size().id()==ID_constant)
  {
    exprt sub_one=gen_one(type.subtype());
    mp_integer s;

    if(sub_one.is_nil() ||
       to_integer(to_vector_type(type).size(), s))
      return sub_one;

    exprt::operandst ops(integer2unsigned(s), sub_one);
    vector_exprt v(to_vector_type(type));
    v.operands().swap(ops);

    return v;
  }
  else
    return nil_exprt();
}

/*******************************************************************\

Function: gen_not

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt gen_unary(const irep_idt &id, const typet &type, const exprt &op);

exprt gen_not(const exprt &op)
{
  return gen_unary(ID_not, bool_typet(), op);
}

/*******************************************************************\

Function: gen_unary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt gen_unary(const irep_idt &id, const typet &type, const exprt &op)
{
  exprt result(id, type);
  result.copy_to_operands(op);
  return result;
}

/*******************************************************************\

Function: gen_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt gen_binary(
  const irep_idt &id,
  const typet &type,
  const exprt &op1,
  const exprt &op2)
{
  exprt result(id, type);
  result.copy_to_operands(op1, op2);
  return result;
}

/*******************************************************************\

Function: make_next_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void make_next_state(exprt &expr)
{
  Forall_operands(it, expr)
    make_next_state(*it);
    
  if(expr.id()==ID_symbol)
    expr.id(ID_next_symbol);
}

/*******************************************************************\

Function: make_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt make_binary(const exprt &expr)
{
  const exprt::operandst &operands=expr.operands();

  if(operands.size()<=2) return expr;

  exprt previous=operands[0];
  
  for(unsigned i=1; i<operands.size(); i++)
  {
    exprt tmp=expr;
    tmp.operands().clear();
    tmp.operands().resize(2);
    tmp.op0().swap(previous);
    tmp.op1()=operands[i];
    previous.swap(tmp);
  }
  
  return previous;
}

/*******************************************************************\

Function: make_with_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

with_exprt make_with_expr(const update_exprt &src)
{
  const exprt::operandst &designator=src.designator();
  assert(!designator.empty());

  with_exprt result;  
  exprt *dest=&result;

  forall_expr(it, designator)
  {
    with_exprt tmp;
  
    if(it->id()==ID_index_designator)
    {
      tmp.where()=to_index_designator(*it).index();
    }
    else if(it->id()==ID_member_designator)
    {
      //irep_idt component_name=
      //  to_member_designator(*it).get_component_name();
    }
    else
      assert(false);
      
    *dest=tmp;
    dest=&to_with_expr(*dest).new_value();
  }
  
  return result;
}

/*******************************************************************\

Function: is_not_zero

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt is_not_zero(
  const exprt &src,
  const namespacet &ns)
{
  // We frequently need to check if a numerical type is not zero.
  // We replace (_Bool)x by x!=0; use ieee_float_notequal for floats.
  // Note that this returns a proper bool_typet(), not a C/C++ boolean.
  // To get a C/C++ boolean, add a further typecast.

  const typet &src_type=ns.follow(src.type());
  
  if(src_type.id()==ID_bool) // already there
    return src; // do nothing
  
  irep_idt id=
    src_type.id()==ID_floatbv?ID_ieee_float_notequal:ID_notequal;
      
  exprt zero=gen_zero(src_type);
  assert(zero.is_not_nil());

  binary_exprt comparison(src, id, zero, bool_typet());
  comparison.add_source_location()=src.source_location();
  
  return comparison;
}

/*******************************************************************\

Function: boolean_negate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt boolean_negate(const exprt &src)
{
  if(src.id()==ID_not && src.operands().size()==1)
    return src.op0();
  else if(src.is_true())
    return false_exprt();
  else if(src.is_false())
    return true_exprt();
  else
    return not_exprt(src);
}
