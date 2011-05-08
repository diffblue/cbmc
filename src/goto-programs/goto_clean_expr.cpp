/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <expr_util.h>
#include <std_expr.h>
#include <rename.h>
#include <cprover_prefix.h>
#include <i2string.h>

#include <ansi-c/c_types.h>

#include "goto_convert_class.h"

/*******************************************************************\

Function: goto_convertt::make_temp_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::make_temp_symbol(
  exprt &expr,
  const std::string &suffix,
  goto_programt &dest)
{
  const locationt location=expr.find_location();
  
  symbolt &new_symbol=
    new_tmp_symbol(expr.type(), suffix, dest, location);

  code_assignt assignment;
  assignment.lhs()=symbol_expr(new_symbol);
  assignment.rhs()=expr;
  assignment.location()=location;

  convert(assignment, dest);

  expr=symbol_expr(new_symbol);  
}

/*******************************************************************\

Function: goto_convertt::needs_cleaning

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool goto_convertt::needs_cleaning(const exprt &expr)
{
  if(expr.id()==ID_index ||
     expr.id()==ID_dereference ||
     expr.id()==ID_sideeffect ||
     expr.id()==ID_struct ||
     expr.id()==ID_array ||
     expr.id()==ID_union ||
     expr.id()==ID_comma)
    return true;
  
  forall_operands(it, expr)
    if(needs_cleaning(*it))
      return true;
      
  return false;
}

/*******************************************************************\

Function: goto_convertt::rewrite_boolean

  Inputs:

 Outputs:

 Purpose: re-write boolean operators into ?:

\*******************************************************************/

void goto_convertt::rewrite_boolean(exprt &expr)
{
  assert(expr.id()==ID_and || expr.id()==ID_or);
  
  if(!expr.is_boolean())
    throw "`"+expr.id_string()+"' "
          "must be Boolean, but got "+expr.pretty();

  // re-write "a && b" into nested a?b:0
  // re-write "a || b" into nested a?1:b

  exprt tmp;
  
  if(expr.id()==ID_and)
    tmp=true_exprt();
  else // ID_or
    tmp=false_exprt();
    
  exprt::operandst &ops=expr.operands();

  // start with last one
  for(int i=int(ops.size())-1; i>=0; i--)
  {
    exprt &op=ops[i];

    if(!op.is_boolean())
     throw "`"+expr.id_string()+"' takes Boolean "
           "operands only, but got "+op.pretty();

    if(expr.id()==ID_and)
    {
      if_exprt if_e(op, tmp, false_exprt());
      tmp.swap(if_e);
    }
    else // ID_or
    {
      if_exprt if_e(op, true_exprt(), tmp);
      tmp.swap(if_e);
    }
  }

  expr.swap(tmp);
}

/*******************************************************************\

Function: goto_convertt::clean_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::clean_expr(
  exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  // this cleans:
  //   && || ?: comma (control-dependency)
  //   function calls
  //   object constructors like arrays, string constants, structs
  //   ++ --
  //   compound assignments

  if(!needs_cleaning(expr)) return;

  if(expr.id()==ID_and || expr.id()==ID_or)
  {
    // rewrite into ?:
    rewrite_boolean(expr);
    
    // recursive call
    clean_expr(expr, dest, result_is_used);
    return;
  }
  else if(expr.id()==ID_if)
  {
    if(expr.operands().size()!=3)
      throw "if takes three arguments";

    if(!expr.op0().is_boolean())
      throw "first argument of `if' must be boolean, but got "
        +expr.op0().to_string();

    // first pull out condition -- we need to prevent
    // this getting destroyed by the side-effects in the other
    // operands
    make_temp_symbol(expr.op0(), "condition", dest);

    // now clean arguments    
    goto_programt tmp_true, tmp_false;
    clean_expr(expr.op1(), tmp_true, result_is_used);
    clean_expr(expr.op2(), tmp_false, result_is_used);

    // generate guard for argument side-effects    
    generate_ifthenelse(
      expr.op0(), tmp_true, tmp_false,
      expr.location(), dest);

    return;
  }
  else if(expr.id()==ID_comma)
  {
    exprt result;
  
    Forall_operands(it, expr)
    {
      bool last=(it==--expr.operands().end());
      
      if(last)
      {
        result.swap(*it);
        clean_expr(result, dest, result_is_used);
      }
      else
        clean_expr(*it, dest, false);
    }
    
    expr.swap(result);
    
    return;
  }
  else if(expr.id()==ID_typecast)
  {
    if(expr.operands().size()!=1)
      throw "typecast takes one argument";

    // preserve 'result_is_used'
    clean_expr(expr.op0(), dest, result_is_used);
    
    return;
  }
  else if(expr.id()==ID_sideeffect)
  {
    // some of the side-effects need special treatment!
    const irep_idt statement=expr.get(ID_statement);
    
    if(statement==ID_gcc_conditional_expression)
    {
      // need to do separately
      remove_gcc_conditional_expression(expr, dest);
      return;
    }
    else if(statement==ID_statement_expression)
    {
      // need to do separately to prevent that
      // the operands of expr get 'cleaned'
      remove_statement_expression(to_side_effect_expr(expr), dest, result_is_used);
      return;
    }
  }

  // TODO: evaluation order

  Forall_operands(it, expr)
    clean_expr(*it, dest);

  if(expr.id()==ID_sideeffect)
  {
    remove_side_effect(to_side_effect_expr(expr), dest, result_is_used);
  }
  else if(expr.id()==ID_address_of)
  {
    assert(expr.operands().size()==1);
    address_of_replace_objects(expr.op0(), dest);
  }
}

/*******************************************************************\

Function: goto_convertt::address_of_replace_objects

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::address_of_replace_objects(
  exprt &expr,
  goto_programt &dest)
{
  if(expr.id()==ID_struct)
    make_temp_symbol(expr, "struct", dest);
  else if(expr.id()==ID_union)
    make_temp_symbol(expr, "union", dest);
  else if(expr.id()==ID_array)
    make_temp_symbol(expr, "array", dest);
  else if(expr.id()==ID_string_constant)
  {
  }
  else
    Forall_operands(it, expr)
      address_of_replace_objects(*it, dest);
}

/*******************************************************************\

Function: goto_convertt::remove_gcc_conditional_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_gcc_conditional_expression(
  exprt &expr,
  goto_programt &dest)
{
  if(expr.operands().size()!=2)
    throw "conditional_expression takes two operands";

  // first remove side-effects from condition
  clean_expr(expr.op0(), dest);

  // now we can copy op0 safely
  if_exprt if_expr;

  if_expr.cond()=expr.op0();
  if_expr.true_case()=expr.op0();
  if_expr.false_case()=expr.op1();
  if_expr.type()=expr.type();
  if_expr.location()=expr.location();

  if(if_expr.cond().type()!=bool_typet())
    if_expr.cond().make_typecast(bool_typet());
  
  expr.swap(if_expr);

  // there might still be junk in expr.op2()  
  clean_expr(expr, dest);
}
