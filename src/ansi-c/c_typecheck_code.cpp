/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <i2string.h>
#include <expr_util.h>

#include "c_typecheck_base.h"

/*******************************************************************\

Function: c_typecheck_baset::init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::start_typecheck_code()
{
  case_is_allowed=break_is_allowed=continue_is_allowed=false;
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_code(codet &code)
{
  if(code.id()!=ID_code)
    throw "expected code, got "+code.pretty();

  code.type()=code_typet();

  const irep_idt &statement=code.get_statement();

  if(statement==ID_expression)
    typecheck_expression(code);
  else if(statement==ID_label)
    typecheck_label(to_code_label(code));
  else if(statement==ID_block)
    typecheck_block(code);
  else if(statement==ID_ifthenelse)
    typecheck_ifthenelse(to_code_ifthenelse(code));
  else if(statement==ID_while ||
          statement==ID_dowhile)
    typecheck_while(code);
  else if(statement==ID_for)
    typecheck_for(code);
  else if(statement==ID_switch)
    typecheck_switch(code);
  else if(statement==ID_break)
    typecheck_break(code);
  else if(statement==ID_goto)
    typecheck_goto(code);
  else if(statement=="computed-goto")
    typecheck_computed_goto(code);
  else if(statement==ID_continue)
    typecheck_continue(code);
  else if(statement==ID_return)
    typecheck_return(code);
  else if(statement==ID_decl)
    typecheck_decl(code);
  else if(statement==ID_decl_type)
    typecheck_decl_type(code);
  else if(statement==ID_decl_block)
    typecheck_decl_block(code);
  else if(statement==ID_assign)
    typecheck_assign(code);
  else if(statement==ID_skip)
  {
  }
  else if(statement==ID_asm)
    typecheck_asm(code);
  else if(statement==ID_start_thread)
    typecheck_start_thread(code);
  else if(statement==ID_gcc_local_label)
    typecheck_gcc_local_label(code);
  else if(statement==ID_msc_try_finally)
  {
    assert(code.operands().size()==2);
    typecheck_code(to_code(code.op0()));
    typecheck_code(to_code(code.op1()));
  }
  else if(statement==ID_msc_try_except)
  {
    assert(code.operands().size()==3);
    typecheck_code(to_code(code.op0()));
    typecheck_expr(code.op1());
    typecheck_code(to_code(code.op2()));
  }
  else if(statement==ID_msc_leave)
  {
    // fine as is, but should check that we
    // are in a 'try' block
  }
  else
  {
    err_location(code);
    str << "unexpected statement: " << statement;
    throw 0;
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_asm

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_asm(codet &code)
{
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_assign(codet &code)
{
  if(code.operands().size()!=2)
    throw "assignment statement expected to have two operands";

  typecheck_expr(code.op0());
  typecheck_expr(code.op1());

  implicit_typecast(code.op1(), code.op0().type());
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_decl_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_decl_block(codet &code)
{
  Forall_operands(it, code)
    typecheck_code(to_code(*it));

  // unwind any decl-blocks inside the decl block
  
  exprt::operandst new_ops;
  new_ops.reserve(code.operands().size());

  Forall_operands(it1, code)
  {
    if(it1->is_nil()) continue;

    codet &code_op=to_code(*it1);
  
    if(code_op.get_statement()==ID_decl_block)
    {
      Forall_operands(it2, code_op)
        if(it2->is_not_nil())
          new_ops.push_back(*it2);
    }
    else
      new_ops.push_back(code_op);
  }

  code.operands().swap(new_ops);
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_block(codet &code)
{
  Forall_operands(it, code)
    typecheck_code(to_code(*it));

  // do decl-blocks

  exprt new_ops;
  new_ops.operands().reserve(code.operands().size());

  Forall_operands(it1, code)
  {
    if(it1->is_nil()) continue;

    codet &code_op=to_code(*it1);
  
    if(code_op.get_statement()==ID_decl_block)
    {
      Forall_operands(it2, code_op)
        if(it2->is_not_nil())
          new_ops.move_to_operands(*it2);
    }
    else if(code_op.get_statement()==ID_label)
    {
      // these may be nested
      codet *code_ptr=&code_op;
      
      while(code_ptr->get_statement()==ID_label)
      {
        assert(code_ptr->operands().size()==1);
        code_ptr=&to_code(code_ptr->op0());
      }
      
      codet &label_op=*code_ptr;

      // move declaration out of label
      if(label_op.get_statement()==ID_decl_block)
      {
        codet tmp;
        tmp.swap(label_op);
        label_op=codet(ID_skip);
        
        new_ops.move_to_operands(code_op);

        Forall_operands(it2, tmp)
          if(it2->is_not_nil())
            new_ops.move_to_operands(*it2);
      }
      else
        new_ops.move_to_operands(code_op);
    }
    else
      new_ops.move_to_operands(code_op);
  }

  code.operands().swap(new_ops.operands());
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_break

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_break(codet &code)
{
  if(!break_is_allowed)
  {
    err_location(code);
    throw "break not allowed here";
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_continue

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_continue(codet &code)
{
  if(!continue_is_allowed)
  {
    err_location(code);
    throw "continue not allowed here";
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_decl_type(codet &code)
{
  assert(code.operands().size()==0);
  // type only!
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_decl(codet &code)
{
  // this may have 1 or 2 operands
  
  if(code.operands().size()!=1 &&
     code.operands().size()!=2)
  {
    err_location(code);
    throw "decl expected to have 1 or 2 arguments";
  }

  // op0 must be symbol
  if(code.op0().id()!=ID_symbol)
  {
    err_location(code);
    throw "decl expected to have symbol as first operand";
  }

  // replace if needed
  replace_symbol(code.op0());

  // look it up
  const irep_idt &identifier=code.op0().get(ID_identifier);

  contextt::symbolst::iterator s_it=context.symbols.find(identifier);

  if(s_it==context.symbols.end())
  {
    err_location(code);
    throw "failed to find decl symbol in context";
  }

  symbolt &symbol=s_it->second;
  
  // see if code got generated for the type
  {
    clean_codet::iterator it=clean_code.find(symbol.name);

    if(it!=clean_code.end())
    {
      codet c=it->second;
      
      // do again
      clean_code.erase(it);
      typecheck_decl(code);
    
      // build a decl-block
      codet decl_block(ID_decl_block);
      decl_block.copy_to_operands(c, code);
      code.swap(decl_block);
      return;
    }
  }

  // see if it's a typedef
  // or a function
  // or static
  if(symbol.is_type ||
     symbol.type.id()==ID_code ||
     symbol.static_lifetime)
  {
    locationt location=code.location();
    code=code_skipt();
    code.location()=location;
    return;
  }

  code.location()=symbol.location;
  
  // check the initializer, if any
  if(code.operands().size()==2)
  {
    typecheck_expr(code.op1());
    do_initializer(code.op1(), symbol.type, false);

    if(follow(symbol.type).id()==ID_incomplete_array)
      symbol.type=code.op1().type();
  }
  
  // set type now (might be changed by initializer)
  code.op0().type()=symbol.type;

  // this must not be an incomplete type
  if(!is_complete_type(code.op0().type()))
  {
    err_location(code);
    throw "incomplete type not permitted here";
  }
}

/*******************************************************************\

Function: c_typecheck_baset::is_complete_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool c_typecheck_baset::is_complete_type(const typet &type) const
{
  if(type.id()==ID_incomplete_struct ||
     type.id()==ID_incomplete_union ||
     type.id()==ID_incomplete_array)
    return false;
  else if(type.id()==ID_array)
    return is_complete_type(type.subtype());
  else if(type.id()==ID_struct || type.id()==ID_union)
  {
    const struct_union_typet::componentst &components=
      to_struct_union_type(type).components();
    for(struct_union_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
      if(!is_complete_type(it->type()))
        return false;
  }
  else if(type.id()==ID_vector)
    return is_complete_type(type.subtype());
  else if(type.id()==ID_symbol)
    return is_complete_type(follow(type));
  
  return true;
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expression(codet &code)
{
  if(code.operands().size()!=1)
    throw "expression statement expected to have one operand";

  exprt &op=code.op0();
  typecheck_expr(op);

  if(op.id()==ID_sideeffect)
  {
    const irep_idt &statement=op.get(ID_statement);
    
    if(statement==ID_assign)
    {
      assert(op.operands().size()==2);
      
      // pull assignment statements up
      exprt::operandst operands;
      operands.swap(op.operands());
      code.set_statement(ID_assign);
      code.operands().swap(operands);
      
      if(code.op1().id()==ID_sideeffect &&
         code.op1().get(ID_statement)==ID_function_call)
      {
        assert(code.op1().operands().size()==2);
  
        code_function_callt function_call;
        function_call.location().swap(code.op1().location());
        function_call.lhs()=code.op0();
        function_call.function()=code.op1().op0();
        function_call.arguments()=code.op1().op1().operands();
        code.swap(function_call);
      }
    }
    else if(statement==ID_function_call)
    {
      assert(op.operands().size()==2);
      
      // pull function calls up
      code_function_callt function_call;
      function_call.location()=code.location();
      function_call.function()=op.op0();
      function_call.arguments()=op.op1().operands();
      code.swap(function_call);
    }
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_for

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_for(codet &code)
{
  if(code.operands().size()!=4)
    throw "for expected to have four operands";
    
  // the "for" statement has an implicit block around it,
  // since code.op0() may contain declarations
  //
  // we therefore transform
  //
  //   for(a;b;c) d;
  //
  // to
  //
  //   { a; for(;b;c) d; }

  if(code.op0().is_nil())
  {
    if(code.op1().is_nil())
      code.op1().make_true();
    else
    {
      typecheck_expr(code.op1());
      implicit_typecast_bool(code.op1());
    }

    if(code.op2().is_not_nil())
      typecheck_expr(code.op2());

    if(code.op3().is_not_nil())
    {
      // save & set flags
      bool old_break_is_allowed=break_is_allowed;
      bool old_continue_is_allowed=continue_is_allowed;

      break_is_allowed=continue_is_allowed=true;

      // recursive call
      typecheck_code(to_code(code.op3()));

      // restore flags
      break_is_allowed=old_break_is_allowed;
      continue_is_allowed=old_continue_is_allowed;
    }
  }
  else
  {
    code_blockt code_block;
    code_block.location()=code.location();

    code_block.reserve_operands(2);
    code_block.move_to_operands(code.op0());
    code.op0().make_nil();
    code_block.move_to_operands(code);
    code.swap(code_block);
    typecheck_code(code); // recursive call
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_label

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_label(code_labelt &code)
{
  if(code.operands().size()!=1)
  {
    err_location(code);
    throw "label expected to have one operand";
  }

  typecheck_code(to_code(code.op0()));

  if(code.is_default())
  {
    if(!case_is_allowed)
    {
      err_location(code);
      throw "did not expect default label here";
    }
  }

  if(code.find(ID_case).is_not_nil())
  {
    if(!case_is_allowed)
    {
      err_location(code);
      throw "did not expect `case' here";
    }

    exprt &case_expr=static_cast<exprt &>(code.add(ID_case));

    Forall_operands(it, case_expr)
    {
      typecheck_expr(*it);
      implicit_typecast(*it, switch_op_type);
    }
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_gcc_local_label

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_gcc_local_label(codet &code)
{
  // these are just declarations, e.g.,
  // __label__ here, there;
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_goto(codet &code)
{
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_computed_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_computed_goto(codet &code)
{
  if(code.operands().size()!=1)
  {
    err_location(code);
    throw "computed-goto expected to have one operand";
  }

  exprt &dest=code.op0();
  
  if(dest.id()!=ID_dereference)
  {
    err_location(dest);
    throw "computed-goto expected to have dereferencing operand";
  }
  
  assert(dest.operands().size()==1);

  typecheck_expr(dest.op0());
  dest.type()=empty_typet();
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_ifthenelse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_ifthenelse(code_ifthenelset &code)
{
  if(code.operands().size()!=2 &&
     code.operands().size()!=3)
    throw "ifthenelse expected to have two or three operands";

  exprt &cond=code.cond();

  typecheck_expr(cond);

  #if 0
  if(cond.id()==ID_sideeffect &&
     cond.get(ID_statement)==ID_assign)
  {
    err_location(cond);
    warning("warning: assignment in if condition");
  }
  #endif

  implicit_typecast_bool(cond);

  typecheck_code(to_code(code.then_case()));

  if(code.operands().size()==3 &&
     !code.else_case().is_nil())
    typecheck_code(to_code(code.else_case()));
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_start_thread

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_start_thread(codet &code)
{
  if(code.operands().size()!=1)
    throw "start_thread expected to have one operand";

  typecheck_code(to_code(code.op0()));
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_return

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_return(codet &code)
{
  if(code.operands().size()==0)
  {
    if(follow(return_type).id()!=ID_empty)
    {
      // gcc doesn't actually complain, it just warns!
      // We'll put a zero here.
      exprt zero=zero_initializer(return_type, code.location());
      code.copy_to_operands(zero);
    }
  }
  else if(code.operands().size()==1)
  {
    typecheck_expr(code.op0());

    if(return_type.id()==ID_empty)
    {
      // gcc doesn't actually complain, it just warns!
      if(code.op0().type().id()!=ID_empty)
        code.op0().make_typecast(return_type);
    }
    else
      implicit_typecast(code.op0(), return_type);
  }
  else
  {
    err_location(code);
    throw "return expected to have 0 or 1 operands";
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_switch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_switch(codet &code)
{
  if(code.operands().size()!=2)
    throw "switch expects two operands";

  typecheck_expr(code.op0());

  // this needs to be promoted
  implicit_typecast_arithmetic(code.op0());

  // save & set flags

  bool old_case_is_allowed(case_is_allowed);
  bool old_break_is_allowed(break_is_allowed);
  typet old_switch_op_type(switch_op_type);

  switch_op_type=code.op0().type();
  break_is_allowed=case_is_allowed=true;

  typecheck_code(to_code(code.op1()));

  // restore flags
  case_is_allowed=old_case_is_allowed;
  break_is_allowed=old_break_is_allowed;
  switch_op_type=old_switch_op_type;
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_while

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_while(codet &code)
{
  if(code.operands().size()!=2)
    throw "while expected to have two operands";

  typecheck_expr(code.op0());
  implicit_typecast_bool(code.op0());

  // save & set flags
  bool old_break_is_allowed(break_is_allowed);
  bool old_continue_is_allowed(continue_is_allowed);

  break_is_allowed=continue_is_allowed=true;

  typecheck_code(to_code(code.op1()));

  // restore flags
  break_is_allowed=old_break_is_allowed;
  continue_is_allowed=old_continue_is_allowed;
}
