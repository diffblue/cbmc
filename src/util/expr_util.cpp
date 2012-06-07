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
     type_id==ID_complex ||
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
  else if(type_id==ID_bool)
  {
    result.make_false();
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
     type_id==ID_natural ||
     type_id==ID_complex)
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

Function: gen_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void gen_binary(exprt &expr, const irep_idt &id, bool default_value)
{
  if(expr.operands().size()==0)
  {
    if(default_value)
      expr.make_true();
    else
      expr.make_false();
  }
  else if(expr.operands().size()==1)
  {
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
  }
  else
  {
    expr.id(id);
    expr.type()=bool_typet();
  }
}

/*******************************************************************\

Function: gen_and

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void gen_and(exprt &expr)
{
  gen_binary(expr, ID_and, true);
}

/*******************************************************************\

Function: gen_or

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void gen_or(exprt &expr)
{
  gen_binary(expr, ID_or, false);
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

