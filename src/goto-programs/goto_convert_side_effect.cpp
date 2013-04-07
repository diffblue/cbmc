/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <expr_util.h>
#include <std_expr.h>
#include <rename.h>
#include <cprover_prefix.h>
#include <i2string.h>
#include <symbol.h>

#include <ansi-c/c_types.h>

#include "goto_convert_class.h"

/*******************************************************************\

Function: goto_convertt::has_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool goto_convertt::has_function_call(const exprt &expr)
{
  forall_operands(it, expr)
    if(has_function_call(*it))
      return true;

  if(expr.id()==ID_sideeffect &&
     expr.get(ID_statement)==ID_function_call)
    return true;

  return false;
}

/*******************************************************************\

Function: goto_convertt::remove_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_assignment(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  const irep_idt statement=expr.get_statement();
  
  if(statement==ID_assign)
  {
    exprt tmp=expr;
    tmp.id(ID_code);
    // just interpret as code
    convert_assign(to_code_assign(to_code(tmp)), dest);
  }
  else if(statement==ID_assign_plus ||
          statement==ID_assign_minus ||
          statement==ID_assign_mult ||
          statement==ID_assign_div ||
          statement==ID_assign_mod ||
          statement==ID_assign_shl ||
          statement==ID_assign_ashr ||
          statement==ID_assign_lshr ||
          statement==ID_assign_bitand ||
          statement==ID_assign_bitxor ||
          statement==ID_assign_bitor)
  {
    if(expr.operands().size()!=2)
    {
      err_location(expr);
      str << statement << " takes two arguments";
      throw 0;
    }

    exprt rhs;

    if(statement==ID_assign_plus)
      rhs.id(ID_plus);
    else if(statement==ID_assign_minus)
      rhs.id(ID_minus);
    else if(statement==ID_assign_mult)
      rhs.id(ID_mult);
    else if(statement==ID_assign_div)
      rhs.id(ID_div);
    else if(statement==ID_assign_mod)
      rhs.id(ID_mod);
    else if(statement==ID_assign_shl)
      rhs.id(ID_shl);
    else if(statement==ID_assign_ashr)
      rhs.id(ID_ashr);
    else if(statement==ID_assign_lshr)
      rhs.id(ID_lshr);
    else if(statement==ID_assign_bitand)
      rhs.id(ID_bitand);
    else if(statement==ID_assign_bitxor)
      rhs.id(ID_bitxor);
    else if(statement==ID_assign_bitor)
      rhs.id(ID_bitor);
    else
    {
      err_location(expr);
      str << "assignment `" << statement << "' not yet supproted";
      throw 0;
    }

    rhs.copy_to_operands(expr.op0(), expr.op1());
    rhs.type()=expr.op0().type();
    
    // bool doesn't really exist as a type,
    // fake promotion!
    if(rhs.op0().type().id()==ID_bool)
    {
      rhs.op0().make_typecast(signed_int_type());
      rhs.op1().make_typecast(signed_int_type());
      rhs.type()=signed_int_type();
      rhs.make_typecast(typet(ID_bool));
    }
    
    exprt lhs=expr.op0();
    
    code_assignt assignment(lhs, rhs);
    assignment.location()=expr.location();
    
    convert(assignment, dest);
  }
  else
    assert(false);

  // revert assignment in the expression to its LHS
  if(result_is_used)
  {
    exprt lhs;
    lhs.swap(expr.op0());
    expr.swap(lhs);
  }
  else
    expr.make_nil();
}

/*******************************************************************\

Function: goto_convertt::remove_pre

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_pre(
  side_effect_exprt &expr,
  goto_programt &dest)
{
  if(expr.operands().size()!=1)
    throw "preincrement/predecrement must have one operand";

  const irep_idt statement=expr.get_statement();

  assert(statement==ID_preincrement ||
         statement==ID_predecrement);

  exprt rhs;

  if(statement==ID_preincrement)
    rhs.id(ID_plus);
  else
    rhs.id(ID_minus);
      
  const typet &op_type=ns.follow(expr.op0().type());
      
  if(op_type.id()==ID_bool)
  {
    rhs.copy_to_operands(expr.op0(), gen_one(signed_int_type()));
    rhs.op0().make_typecast(signed_int_type());
    rhs.type()=signed_int_type();
    rhs.make_typecast(typet(ID_bool));
  }
  else if(op_type.id()==ID_c_enum ||
          op_type.id()==ID_incomplete_c_enum)
  {
    rhs.copy_to_operands(expr.op0(), gen_one(signed_int_type()));
    rhs.op0().make_typecast(signed_int_type());
    rhs.type()=signed_int_type();
    rhs.make_typecast(op_type);
  }
  else
  {
    typet constant_type;

    if(op_type.id()==ID_pointer)
      constant_type=index_type();
    else if(is_number(op_type))
      constant_type=op_type;
    else
    {
      err_location(expr);
      throw "no constant one of type "+op_type.to_string();
    }

    exprt constant=gen_one(constant_type);

    rhs.copy_to_operands(expr.op0());
    rhs.move_to_operands(constant);
    rhs.type()=expr.op0().type();
  }

  code_assignt assignment(expr.op0(), rhs);
  assignment.location()=expr.find_location();
  
  convert(assignment, dest);

  // revert to argument of pre-inc/pre-dec
  exprt op=expr.op0();
  expr.swap(op);
}

/*******************************************************************\

Function: goto_convertt::remove_post

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_post(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  goto_programt tmp1, tmp2;

  // we have ...(op++)...

  if(expr.operands().size()!=1)
    throw "postincrement/postdecrement must have one operand";

  const irep_idt statement=expr.get_statement();

  assert(statement==ID_postincrement ||
         statement==ID_postdecrement);

  exprt rhs;

  if(statement==ID_postincrement)
    rhs.id(ID_plus);
  else
    rhs.id(ID_minus);
    
  const typet &op_type=ns.follow(expr.op0().type());
    
  if(op_type.id()==ID_bool)
  {
    rhs.copy_to_operands(expr.op0(), gen_one(signed_int_type()));
    rhs.op0().make_typecast(signed_int_type());
    rhs.type()=signed_int_type();
    rhs.make_typecast(typet(ID_bool));
  }
  else if(op_type.id()==ID_c_enum ||
          op_type.id()==ID_incomplete_c_enum)
  {
    rhs.copy_to_operands(expr.op0(), gen_one(signed_int_type()));
    rhs.op0().make_typecast(signed_int_type());
    rhs.type()=signed_int_type();
    rhs.make_typecast(op_type);
  }
  else
  {
    typet constant_type;

    if(op_type.id()==ID_pointer)
      constant_type=index_type();
    else if(is_number(op_type))
      constant_type=op_type;
    else
    {
      err_location(expr);
      throw "no constant one of type "+op_type.to_string();
    }

    exprt constant=gen_one(constant_type);

    rhs.copy_to_operands(expr.op0());
    rhs.move_to_operands(constant);
    rhs.type()=expr.op0().type();
  }

  code_assignt assignment(expr.op0(), rhs);
  assignment.location()=expr.find_location();
  
  convert(assignment, tmp2);

  // fix up the expression, if needed

  if(result_is_used)
  {
    exprt tmp=expr.op0();
    make_temp_symbol(tmp, "post", dest);
    expr.swap(tmp);
  }
  else
    expr.make_nil();

  dest.destructive_append(tmp1);
  dest.destructive_append(tmp2);
}

/*******************************************************************\

Function: goto_convertt::remove_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_function_call(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  if(!result_is_used)
  {
    assert(expr.operands().size()==2);
    code_function_callt call;
    call.function()=expr.op0();
    call.arguments()=expr.op1().operands();
    call.location()=expr.location();
    call.lhs().make_nil();
    convert_function_call(call, dest);
    expr.make_nil();
    return;
  }

  symbolt new_symbol;

  new_symbol.base_name="return_value";
  new_symbol.is_lvalue=true;
  new_symbol.is_state_var=true;
  new_symbol.is_file_local=true;
  new_symbol.is_thread_local=true;
  new_symbol.type=expr.type();
  new_symbol.location=expr.find_location();

  // get name of function, if available

  if(expr.id()!=ID_sideeffect ||
     expr.get(ID_statement)!=ID_function_call)
    throw "expected function call";

  if(expr.operands().empty())
    throw "function_call expects at least one operand";

  if(expr.op0().id()==ID_symbol)
  {
    const irep_idt &identifier=expr.op0().get(ID_identifier);
    const symbolt &symbol=lookup(identifier);
    
    std::string new_base_name=id2string(new_symbol.base_name);
    
    new_base_name+="_";
    new_base_name+=id2string(symbol.base_name);
    new_base_name+="$"+i2string(++temporary_counter);
    
    new_symbol.base_name=new_base_name;
    new_symbol.mode=symbol.mode;
  }

  new_symbol.name=tmp_symbol_prefix+id2string(new_symbol.base_name);

  new_name(new_symbol);
  
  tmp_symbols.push_back(new_symbol.name);
  
  {
    code_declt decl;
    decl.symbol()=symbol_expr(new_symbol);
    decl.location()=new_symbol.location;
    convert_decl(decl, dest);
  }

  {
    goto_programt tmp_program2;
    code_function_callt call;
    call.lhs()=symbol_expr(new_symbol);
    call.function()=expr.op0();
    call.arguments()=expr.op1().operands();
    call.location()=new_symbol.location;
    convert_function_call(call, dest);
  }

  static_cast<exprt &>(expr)=symbol_expr(new_symbol);
}

/*******************************************************************\

Function: goto_convertt::replace_new_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::replace_new_object(
  const exprt &object,
  exprt &dest)
{
  if(dest.id()=="new_object")
    dest=object;
  else
    Forall_operands(it, dest)
      replace_new_object(object, *it);
}

/*******************************************************************\

Function: goto_convertt::remove_cpp_new

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_cpp_new(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  codet call;

  symbolt new_symbol;

  new_symbol.base_name="new_ptr$"+i2string(++temporary_counter);
  new_symbol.is_lvalue=true;
  new_symbol.type=expr.type();
  new_symbol.is_file_local=true;
  new_symbol.name=tmp_symbol_prefix+id2string(new_symbol.base_name);

  new_name(new_symbol);
  tmp_symbols.push_back(new_symbol.name);

  call=code_assignt(symbol_expr(new_symbol), expr);

  if(result_is_used)
    static_cast<exprt &>(expr)=symbol_expr(new_symbol);
  else
    expr.make_nil();

  convert(call, dest);
}

/*******************************************************************\

Function: goto_convertt::remove_cpp_delete

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_cpp_delete(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  assert(expr.operands().size()==1);

  codet tmp;
  
  tmp.set_statement(expr.get_statement());
  tmp.location()=expr.location();
  tmp.copy_to_operands(expr.op0());
  tmp.set(ID_destructor, expr.find(ID_destructor));

  convert_cpp_delete(tmp, dest);
  
  expr.make_nil();  
}

/*******************************************************************\

Function: goto_convertt::remove_malloc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_malloc(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  codet call;

  if(result_is_used)
  {
    symbolt new_symbol;

    new_symbol.base_name="new_value$"+i2string(++temporary_counter);
    new_symbol.is_lvalue=true;
    new_symbol.is_file_local=true;
    new_symbol.type=expr.type();
    new_symbol.name=tmp_symbol_prefix+id2string(new_symbol.base_name);

    new_name(new_symbol);
    tmp_symbols.push_back(new_symbol.name);

    call=code_assignt(symbol_expr(new_symbol), expr);
    
    static_cast<exprt &>(expr)=symbol_expr(new_symbol);
  }
  else
  {
    call=codet(ID_expression);
    call.move_to_operands(expr);
  }

  convert(call, dest);
}

/*******************************************************************\

Function: goto_convertt::remove_temporary_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_temporary_object(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  if(expr.operands().size()!=1 &&
     expr.operands().size()!=0)
    throw "temporary_object takes 0 or 1 operands";

  symbolt &new_symbol=
    new_tmp_symbol(expr.type(), "obj", dest, expr.find_location());

  new_symbol.mode=expr.get(ID_mode);
  
  if(expr.operands().size()==1)
  {
    codet assignment(ID_assign);
    assignment.reserve_operands(2);
    assignment.copy_to_operands(symbol_expr(new_symbol));
    assignment.move_to_operands(expr.op0());

    convert(assignment, dest);
  }

  if(expr.find(ID_initializer).is_not_nil())
  {
    assert(expr.operands().empty());
    exprt initializer=static_cast<const exprt &>(expr.find(ID_initializer));
    replace_new_object(symbol_expr(new_symbol), initializer);

    convert(to_code(initializer), dest);
  }

  static_cast<exprt &>(expr)=symbol_expr(new_symbol);  
}

/*******************************************************************\

Function: goto_convertt::remove_statement_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_statement_expression(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  // This is a gcc extension of the form ({ ....; expr; })
  // The value is that of the final expression.
  // The expression is copied into a temporary before the
  // scope is destoyed.

  if(expr.operands().size()!=1)
    throw "statement_expression takes 1 operand";

  if(expr.op0().id()!=ID_code)
    throw "statement_expression takes code as operand";

  codet &code=to_code(expr.op0());

  if(!result_is_used)
  {
    convert(code, dest);
    expr.make_nil();
    return;
  }
  
  // get last statement from block
  codet *last=&code;
    
  while(true)
  {
    if(last->get_statement()==ID_block)
    {
      if(last->operands().empty())
        throw "statement_expression expects non-empty block";
      
      last=&to_code(last->operands().back());
    }
    else if(last->get_statement()==ID_label)
    {
      assert(last->operands().size()==1);
      last=&to_code(last->op0());
    }
    else
      break;
  }

  codet old_last=*last;
  if(last->get(ID_statement)==ID_expression)
    last->set_statement(ID_skip);
  
  convert(code, dest);

  {
    clean_expr(old_last, dest, true);

    if(old_last.get(ID_statement)==ID_expression &&
       old_last.operands().size()==1)
      static_cast<exprt &>(expr)=to_code_expression(old_last).expression();
    else if(old_last.get(ID_statement)==ID_assign)
      static_cast<exprt &>(expr)=to_code_assign(old_last).lhs();
    else
    {
      std::stringstream str;
      str << "statement_expression expects expression as "
            "last statement, but got `"+
            id2string(old_last.get(ID_statement))+"'";
      if(dest.instructions.size() > 0)
    	str << " - error may be at: " << dest.instructions.back().location;
      throw str.str();
    }
  }
}

/*******************************************************************\

Function: goto_convertt::remove_side_effect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_side_effect(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  const irep_idt &statement=expr.get_statement();
  
  if(statement==ID_function_call)
    remove_function_call(expr, dest, result_is_used);
  else if(statement==ID_assign ||
          statement==ID_assign_plus ||
          statement==ID_assign_minus ||
          statement==ID_assign_mult ||
          statement==ID_assign_div ||
          statement==ID_assign_bitor ||
          statement==ID_assign_bitxor ||
          statement==ID_assign_bitand ||
          statement==ID_assign_lshr ||
          statement==ID_assign_ashr ||
          statement==ID_assign_shl ||
          statement==ID_assign_mod)
    remove_assignment(expr, dest, result_is_used);
  else if(statement==ID_postincrement ||
          statement==ID_postdecrement)
    remove_post(expr, dest, result_is_used);
  else if(statement==ID_preincrement ||
          statement==ID_predecrement)
    remove_pre(expr, dest);
  else if(statement==ID_cpp_new ||
          statement==ID_cpp_new_array)
    remove_cpp_new(expr, dest, result_is_used);
  else if(statement==ID_cpp_delete ||
          statement==ID_cpp_delete_array)
    remove_cpp_delete(expr, dest, result_is_used);
  else if(statement==ID_malloc)
    remove_malloc(expr, dest, result_is_used);
  else if(statement==ID_temporary_object)
    remove_temporary_object(expr, dest, result_is_used);
  else if(statement==ID_statement_expression)
    remove_statement_expression(expr, dest, result_is_used);
  else if(statement==ID_nondet)
  {
    // these are fine
  }
  else if(statement==ID_skip)
  {
    expr.make_nil();
  }
  else if(statement==ID_throw)
  {
    goto_programt::targett t=dest.add_instruction(THROW);
    t->code=codet(ID_throw);
    t->code.operands().swap(expr.operands());
    t->code.location()=expr.location();
    t->location=expr.location();
    t->code.set(ID_exception_list, expr.find(ID_exception_list));
 
    // the result can't be used, these are void
    expr.make_nil();
  }
  else
  {
    str << "cannot remove side effect (" << statement << ")";
    throw 0;
  }
}

