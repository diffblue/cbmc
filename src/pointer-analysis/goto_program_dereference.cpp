/*******************************************************************\

Module: Dereferencing Operations on GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <simplify_expr.h>
#include <base_type.h>
#include <std_code.h>
#include <context.h>
#include <guard.h>
#include <options.h>

#include "goto_program_dereference.h"

/*******************************************************************\

Function: goto_program_dereferencet::has_failed_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool goto_program_dereferencet::has_failed_symbol(
  const exprt &expr,
  const symbolt *&symbol)
{
  if(expr.id()==ID_symbol)
  {
    if(expr.get_bool("#invalid_object"))
      return false;

    const symbolt &ptr_symbol=ns.lookup(expr);

    const irep_idt &failed_symbol=
      ptr_symbol.type.get("#failed_symbol");    
      
    if(failed_symbol==irep_idt()) return false;

    return !ns.lookup(failed_symbol, symbol);
  }
  
  return false;
}

/*******************************************************************\

Function: goto_program_dereferencet::is_valid_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool goto_program_dereferencet::is_valid_object(
  const irep_idt &identifier)
{
  const symbolt &symbol=ns.lookup(identifier);

  if(symbol.type.id()==ID_code)
    return true;

  if(symbol.static_lifetime)
    return true; // global/static

  #if 0
  if(valid_local_variables->find(symbol.name)!=
     valid_local_variables->end())
    return true; // valid local
  #else
  return true;
  #endif

  return false;
}

/*******************************************************************\

Function: goto_program_dereferencet::dereference_failure

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_program_dereferencet::dereference_failure(
  const std::string &property,
  const std::string &msg,
  const guardt &guard)
{
  exprt guard_expr=guard.as_expr();
  
  if(assertions.insert(guard_expr).second)
  {
    guard_expr.make_not();

    // first try simplifier on it
    if(options.get_bool_option("simplify"))
      simplify(guard_expr, ns);
  
    if(!guard_expr.is_true())
    {
      goto_program_instruction_typet type=
        options.get_bool_option("assert-to-assume")?ASSUME:ASSERT;

      goto_programt::targett t=new_code.add_instruction(type);
      t->guard.swap(guard_expr);
      t->location=dereference_location;
      t->location.set(ID_property, property);
      t->location.set(ID_comment, "dereference failure: "+msg);
    }
  }
}

/*******************************************************************\

Function: goto_program_dereferencet::dereference_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_program_dereferencet::dereference_rec(
  exprt &expr,
  guardt &guard,
  const dereferencet::modet mode)
{
  if(!dereference.has_dereference(expr))
    return;

  if(expr.id()==ID_and || expr.id()==ID_or)
  {
    if(!expr.is_boolean())
      throw expr.id_string()+" must be Boolean, but got "+
            expr.pretty();

    unsigned old_guards=guard.size();

    for(unsigned i=0; i<expr.operands().size(); i++)
    {
      exprt &op=expr.operands()[i];

      if(!op.is_boolean())
        throw expr.id_string()+" takes Boolean operands only, but got "+
              op.pretty();

      if(dereference.has_dereference(op))
        dereference_rec(op, guard, dereferencet::READ);

      if(expr.id()==ID_or)
      {
        exprt tmp(op);
        tmp.make_not();
        guard.add(tmp);
      }
      else
        guard.add(op);
    }

    guard.resize(old_guards);

    return;
  }
  else if(expr.id()==ID_if)
  {
    if(expr.operands().size()!=3)
      throw "if takes three arguments";

    if(!expr.op0().is_boolean())
    {
      std::string msg=
        "first argument of if must be boolean, but got "
        +expr.op0().to_string();
      throw msg;
    }

    dereference_rec(expr.op0(), guard, dereferencet::READ);

    bool o1=dereference.has_dereference(expr.op1());
    bool o2=dereference.has_dereference(expr.op2());

    if(o1)
    {
      unsigned old_guard=guard.size();
      guard.add(expr.op0());
      dereference_rec(expr.op1(), guard, mode);
      guard.resize(old_guard);
    }

    if(o2)
    {
      unsigned old_guard=guard.size();
      exprt tmp(expr.op0());
      tmp.make_not();
      guard.add(tmp);
      dereference_rec(expr.op2(), guard, mode);
      guard.resize(old_guard);
    }

    return;
  }

  if(expr.id()==ID_address_of ||
     expr.id()=="reference_to")
  {
    // turn &*p to p
    // this has *no* side effect!
    
    assert(expr.operands().size()==1);
    
    if(expr.op0().id()==ID_dereference ||
       expr.op0().id()=="implicit_dereference")
    {
      assert(expr.op0().operands().size()==1);

      exprt tmp;
      tmp.swap(expr.op0().op0());
      
      if(tmp.type()!=expr.type())
        tmp.make_typecast(expr.type());

      expr.swap(tmp);      
    }
  }

  Forall_operands(it, expr)
    dereference_rec(*it, guard, mode);

  if(expr.id()==ID_dereference)
  {
    if(expr.operands().size()!=1)
      throw "dereference expects one operand";

    dereference_location=expr.find_location();

    exprt tmp=dereference.dereference(
      expr.op0(), guard, mode);

    expr.swap(tmp);
  }
  else if(expr.id()=="implicit_dereference")
  {
    // old stuff
    assert(false);
  }
  else if(expr.id()==ID_index)
  {
    // this is old stuff and will go away

    if(expr.operands().size()!=2)
      throw "index expects two operands";

    if(expr.op0().type().id()==ID_pointer)
    {
      dereference_location=expr.find_location();

      exprt tmp1(ID_plus, expr.op0().type());
      tmp1.operands().swap(expr.operands());
      
      exprt tmp2=dereference.dereference(tmp1, guard, mode);
      tmp2.swap(expr);
    }
  }
}

/*******************************************************************\

Function: goto_program_dereferencet::get_value_set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_program_dereferencet::get_value_set(
  const exprt &expr,
  value_setst::valuest &dest)
{
  value_sets.get_values(current_target, expr, dest);
}

/*******************************************************************\

Function: goto_program_dereferencet::dereference_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_program_dereferencet::dereference_expr(
  exprt &expr,
  const bool checks_only,
  const dereferencet::modet mode)
{
  guardt guard;
  
  if(checks_only)
  {
    exprt tmp(expr);
    dereference_rec(tmp, guard, mode);
  }
  else
    dereference_rec(expr, guard, mode);
}

/*******************************************************************\

Function: goto_program_dereferencet::dereference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_program_dereferencet::dereference_program(
  goto_programt &goto_program,
  bool checks_only)
{
  for(goto_programt::instructionst::iterator
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++)
  {
    new_code.clear();
    assertions.clear();

    dereference_instruction(it, checks_only);  
    
    // insert new instructions
    while(!new_code.instructions.empty())
    {
      goto_program.insert_before_swap(it, new_code.instructions.front());
      new_code.instructions.pop_front();
      it++;
    }
  }
}

/*******************************************************************\

Function: goto_program_dereferencet::dereference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_program_dereferencet::dereference_program(
  goto_functionst &goto_functions,
  bool checks_only)
{
  for(goto_functionst::function_mapt::iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    dereference_program(it->second.body, checks_only);
}

/*******************************************************************\

Function: goto_program_dereferencet::dereference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_program_dereferencet::dereference_instruction(
  goto_programt::targett target,
  bool checks_only)
{
  current_target=target;
  #if 0
  valid_local_variables=&target->local_variables;
  #endif
  goto_programt::instructiont &i=*target;

  dereference_expr(i.guard, checks_only, dereferencet::READ);

  if(i.is_assign())
  {
    if(i.code.operands().size()!=2)
      throw "assignment expects two operands";

    dereference_expr(i.code.op0(), checks_only, dereferencet::WRITE);
    dereference_expr(i.code.op1(), checks_only, dereferencet::READ);
  }
  else if(i.is_function_call())
  {
    code_function_callt &function_call=to_code_function_call(to_code(i.code));
    
    if(function_call.lhs().is_not_nil())
      dereference_expr(function_call.lhs(), checks_only, dereferencet::WRITE);
    
    dereference_expr(function_call.function(), checks_only, dereferencet::READ);
    dereference_expr(function_call.op2(), checks_only, dereferencet::READ);
  }
  else if(i.is_return())
  {
    Forall_operands(it, i.code)
      dereference_expr(*it, checks_only, dereferencet::READ);
  }
  else if(i.is_other())
  {
    const irep_idt &statement=i.code.get(ID_statement);

    if(statement==ID_expression)
    {
      if(i.code.operands().size()!=1)
        throw "expression expects one operand";

      dereference_expr(i.code.op0(), checks_only, dereferencet::READ);
    }
    else if(statement==ID_printf)
    {
      Forall_operands(it, i.code)
        dereference_expr(*it, checks_only, dereferencet::READ);
    }
  }
}

/*******************************************************************\

Function: goto_program_dereferencet::dereference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_program_dereferencet::dereference_expression(
  goto_programt::const_targett target,
  exprt &expr)
{
  current_target=target;
  #if 0
  valid_local_variables=&target->local_variables;
  #endif

  dereference_expr(expr, false, dereferencet::READ);
}

/*******************************************************************\

Function: goto_program_dereferencet::pointer_checks

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_program_dereferencet::pointer_checks(
  goto_programt &goto_program)
{
  dereference_program(goto_program, true);
}

/*******************************************************************\

Function: goto_program_dereferencet::pointer_checks

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_program_dereferencet::pointer_checks(
  goto_functionst &goto_functions)
{
  dereference_program(goto_functions, true);
}

/*******************************************************************\

Function: remove_pointers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void remove_pointers(
  goto_programt &goto_program,
  contextt &context,
  value_setst &value_sets)
{
  namespacet ns(context);
  
  optionst options;

  goto_program_dereferencet
    goto_program_dereference(ns, context, options, value_sets);

  goto_program_dereference.dereference_program(goto_program);
}                    

/*******************************************************************\

Function: remove_pointers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void remove_pointers(
  goto_functionst &goto_functions,
  contextt &context,
  value_setst &value_sets)
{
  namespacet ns(context);
  
  optionst options;

  goto_program_dereferencet
    goto_program_dereference(ns, context, options, value_sets);

  Forall_goto_functions(it, goto_functions)
    goto_program_dereference.dereference_program(it->second.body);
}                    

/*******************************************************************\

Function: pointer_checks

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void pointer_checks(
  goto_programt &goto_program,
  contextt &context,
  const optionst &options,
  value_setst &value_sets)
{
  namespacet ns(context);
  goto_program_dereferencet
    goto_program_dereference(ns, context, options, value_sets);
  goto_program_dereference.pointer_checks(goto_program);
}                    

/*******************************************************************\

Function: pointer_checks

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void pointer_checks(
  goto_functionst &goto_functions,
  contextt &context,
  const optionst &options,
  value_setst &value_sets)
{
  namespacet ns(context);
  goto_program_dereferencet
    goto_program_dereference(ns, context, options, value_sets);
  goto_program_dereference.pointer_checks(goto_functions);
}                    

/*******************************************************************\

Function: dereference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dereference(
  goto_programt::const_targett target,
  exprt &expr,
  const namespacet &ns,
  value_setst &value_sets)
{
  optionst options;
  contextt new_context;
  goto_program_dereferencet
    goto_program_dereference(ns, new_context, options, value_sets);
  goto_program_dereference.dereference_expression(target, expr);
}
