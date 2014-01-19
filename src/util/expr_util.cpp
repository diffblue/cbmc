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

/*******************************************************************\

Function: gen_zero

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt gen_zero(const typet &type)
{
  exprt result;

  const irep_idt type_id=type.id();

  result=constant_exprt(type);

  if(type_id==ID_rational ||
     type_id==ID_real ||
     type_id==ID_integer ||
     type_id==ID_natural ||
     type_id==ID_c_enum)
  {
    result.set(ID_value, ID_0);
  }
  else if(type_id==ID_unsignedbv ||
          type_id==ID_signedbv ||
          type_id==ID_verilogbv ||
          type_id==ID_floatbv ||
          type_id==ID_fixedbv)
  {
    std::string value;
    unsigned width=to_bitvector_type(type).get_width();

    for(unsigned i=0; i<width; i++)
      value+='0';

    result.set(ID_value, value);
  }
  else if(type_id==ID_complex)
  {
    result=exprt(ID_complex, type);
    exprt sub_zero=gen_zero(type.subtype());
    result.operands().resize(2, sub_zero);
  }
  else if(type_id==ID_bool)
  {
    result=false_exprt();
  }
  else if(type_id==ID_pointer)
  {
    result.set(ID_value, ID_NULL);
  }
  else
    result.make_nil();

  return result;
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
  exprt result=constant_exprt(type);

  if(type_id==ID_bool ||
     type_id==ID_rational ||
     type_id==ID_real ||
     type_id==ID_integer ||
     type_id==ID_natural)
  {
    result.set(ID_value, ID_1);
  }
  else if(type_id==ID_unsignedbv ||
          type_id==ID_signedbv ||
          type_id==ID_c_enum)
  {
    std::string value;
    unsigned width=to_bitvector_type(type).get_width();
    for(unsigned i=0; i<width-1; i++)
      value+='0';
    value+='1';
    result.set(ID_value, value);
  }
  else if(type_id==ID_fixedbv)
  {
    fixedbvt fixedbv;
    fixedbv.spec=to_fixedbv_type(type);
    fixedbv.from_integer(1);
    result=fixedbv.to_expr();
  }
  else if(type_id==ID_floatbv)
  {
    ieee_floatt ieee_float;
    ieee_float.spec=to_floatbv_type(type);
    ieee_float.from_integer(1);
    result=ieee_float.to_expr();
  }
  else if(type_id==ID_complex)
  {
    result=exprt(ID_complex, type);
    result.operands().resize(2);
    result.op0()=gen_one(type.subtype());
    result.op1()=gen_zero(type.subtype());
  }
  else
    result.make_nil();

  return result;
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

Function: symbol_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt symbol_expr(const symbolt &symbol)
{
  symbol_exprt tmp(symbol.type);
  tmp.set_identifier(symbol.name);
  return tmp;
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
  comparison.location()=src.location();
  
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
