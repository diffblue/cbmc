/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/expr_util.h>
#include <util/std_expr.h>
#include <util/rename.h>
#include <util/cprover_prefix.h>
#include <util/i2string.h>

#include <ansi-c/c_types.h>

#include "goto_convert_class.h"

/*******************************************************************\

Function: goto_convertt::make_static_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt goto_convertt::make_static_symbol(
  const exprt &expr,
  const std::string &suffix,
  goto_programt &dest)
{
  const locationt location=expr.find_location();
  
  symbolt new_symbol;
  symbolt *symbol_ptr;
  
  do
  {
    new_symbol.base_name="static_"+suffix+"$"+i2string(++temporary_counter);
    new_symbol.name=tmp_symbol_prefix+id2string(new_symbol.base_name);
    new_symbol.is_lvalue=true;
    new_symbol.is_thread_local=false;
    new_symbol.is_static_lifetime=true;
    new_symbol.is_file_local=true;
    new_symbol.value=expr;
    new_symbol.type=expr.type();
    new_symbol.location=location;
  }
  while(symbol_table.move(new_symbol, symbol_ptr));    

  // The value might depend on a variable, thus
  // generate code for this.

  symbol_exprt result=symbol_expr(*symbol_ptr);
  result.location()=location;
  
  code_assignt code_assign(result, expr);
  code_assign.location()=location;
  convert(code_assign, dest);

  return result;
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

  // We can't flatten quantified expressions by introducing new literals for
  // conditional expressions.  This is because the body of the quantified
  // may refer to bound variables, which are not visible outside the scope
  // of the quantifier.
  //
  // For example, the following transformation would not be valid:
  //
  // forall (i : int) (i == 0 || i > 10)
  //
  //   transforming to
  //
  // g1 = (i == 0)
  // g2 = (i > 10)
  // forall (i : int) (g1 || g2)
  if(expr.id()==ID_forall || expr.id()==ID_exists)
    return false;
  
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
    // first clean condition
    clean_expr(to_if_expr(expr).cond(), dest, true);

    // possibly done now
    if(!needs_cleaning(to_if_expr(expr).true_case()) &&
       !needs_cleaning(to_if_expr(expr).false_case()))
      return;

    // copy expression
    if_exprt if_expr=to_if_expr(expr);

    if(!if_expr.cond().is_boolean())
      throw "first argument of `if' must be boolean, but got "
        +if_expr.cond().to_string();

    const locationt location=expr.find_location();
  
    goto_programt tmp_true;
    clean_expr(if_expr.true_case(), tmp_true, result_is_used);

    goto_programt tmp_false;
    clean_expr(if_expr.false_case(), tmp_false, result_is_used);
    
    if(result_is_used)
    {
      symbolt &new_symbol=
        new_tmp_symbol(expr.type(), "if_expr", dest, location);

      code_assignt assignment_true;
      assignment_true.lhs()=symbol_expr(new_symbol);
      assignment_true.rhs()=if_expr.true_case();
      assignment_true.location()=location;
      convert(assignment_true, tmp_true);

      code_assignt assignment_false;
      assignment_false.lhs()=symbol_expr(new_symbol);
      assignment_false.rhs()=if_expr.false_case();
      assignment_false.location()=location;
      convert(assignment_false, tmp_false);

      // overwrites expr
      expr=symbol_expr(new_symbol);  
    }
    else
    {
      // preserve the expressions for possible later checks
      if(if_expr.true_case().is_not_nil())
      {
        code_expressiont code_expression(if_expr.true_case());
        convert(code_expression, tmp_true);
      }
      
      if(if_expr.false_case().is_not_nil())
      {
        code_expressiont code_expression(if_expr.false_case());
        convert(code_expression, tmp_false);
      }
      
      expr=nil_exprt();
    }

    // generate guard for argument side-effects    
    generate_ifthenelse(
      if_expr.cond(), tmp_true, tmp_false,
      location, dest);

    return;
  }
  else if(expr.id()==ID_comma)
  {
    if(result_is_used)
    {
      exprt result;
    
      Forall_operands(it, expr)
      {
        bool last=(it==--expr.operands().end());
        
        // special treatment for last one
        if(last)
        {
          result.swap(*it);
          clean_expr(result, dest, true);
        }
        else
        {
          clean_expr(*it, dest, false);

          // remember these for later checks
          if(it->is_not_nil())
            convert(code_expressiont(*it), dest);
        }
      }

      expr.swap(result);
    }
    else // result not used
    {
      Forall_operands(it, expr)
      {
        clean_expr(*it, dest, false);

        // remember as expression statement for later checks
        if(it->is_not_nil())
          convert(code_expressiont(*it), dest);
      }
      
      expr=nil_exprt();
    }
    
    return;
  }
  else if(expr.id()==ID_typecast)
  {
    if(expr.operands().size()!=1)
      throw "typecast takes one argument";

    // preserve 'result_is_used'
    clean_expr(expr.op0(), dest, result_is_used);
    
    if(expr.op0().is_nil())
      expr.make_nil();
    
    return;
  }
  else if(expr.id()==ID_sideeffect)
  {
    // some of the side-effects need special treatment!
    const irep_idt statement=to_side_effect_expr(expr).get_statement();
    
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
    else if(statement==ID_assign)
    {
      // we do a special treatment for x=f(...)
      assert(expr.operands().size()==2);

      if(expr.op1().id()==ID_sideeffect &&
         to_side_effect_expr(expr.op1()).get_statement()==ID_function_call)
      {
        clean_expr(expr.op0(), dest);
        exprt lhs=expr.op0();

        // turn into code
        code_assignt assignment;
        assignment.lhs()=lhs;
        assignment.rhs()=expr.op1();
        assignment.location()=expr.location();
        convert_assign(assignment, dest);

        if(result_is_used)
          expr.swap(lhs);
        else
          expr.make_nil();
        return;
      }
    }
    else if(statement==ID_function_call)
    {
      if(to_side_effect_expr_function_call(expr).function().id()==ID_symbol &&
         to_symbol_expr(to_side_effect_expr_function_call(expr).function()).get_identifier()=="c::__noop")
      {
        // __noop needs special treatment, as arguments are not
        // evaluated
        to_side_effect_expr_function_call(expr).arguments().clear();
      }
    }
  }
  else if(expr.id()==ID_forall || expr.id()==ID_exists)
  {
    assert(expr.operands().size()==2);
    // check if there are side-effects
    goto_programt tmp;
    clean_expr(expr.op1(), tmp, true);
    if(tmp.instructions.empty())
      throw "no side-effects in quantified expressions allowed";
    return;
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
    expr=make_static_symbol(expr, "struct", dest);
  else if(expr.id()==ID_union)
    expr=make_static_symbol(expr, "union", dest);
  else if(expr.id()==ID_array)
    expr=make_static_symbol(expr, "array", dest);
  else if(expr.id()==ID_string_constant)
  {
    // Leave for now, but long-term these might become static symbols.
    // LLVM appears to do precisely that.
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
