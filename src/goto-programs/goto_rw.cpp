/*******************************************************************\

Module: 

Author: Daniel Kroening

Date: April 2010

\*******************************************************************/

#include <util/std_expr.h>

#include "goto_rw.h"

/*******************************************************************\

Function: get_objects_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typedef enum { LHS_W, READ } get_modet;

void get_objects_rec(
  get_modet mode,
  const exprt &expr,
  std::list<exprt> &read,
  std::list<exprt> &write)
{
  if(expr.id()==ID_symbol)
  {
    if(mode==LHS_W)
      write.push_back(expr);
    else
      read.push_back(expr);
  }
  else if(expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(expr);

    if(mode==READ)
      get_objects_rec(READ, index_expr.index(), read, write);

    get_objects_rec(mode, index_expr.array(), read, write);
  }
  else if(expr.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(expr);

    if(mode==READ)
      get_objects_rec(READ, if_expr.cond(), read, write);

    get_objects_rec(mode, if_expr.true_case(), read, write);
    get_objects_rec(mode, if_expr.false_case(), read, write);
  }
  else if(expr.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(expr);

    get_objects_rec(mode, member_expr.struct_op(), read, write);
  }
  else if(expr.id()==ID_dereference)
  {
    const dereference_exprt &dereference_expr=
      to_dereference_expr(expr);
      
    if(mode==READ)
      get_objects_rec(READ, dereference_expr.pointer(), read, write);

    if(mode==LHS_W)
      write.push_back(expr);
    else
      read.push_back(expr);
  }
  else
  {
    if(mode==READ)
      forall_operands(it, expr)
        get_objects_rec(READ, *it, read, write);
  }
}

/*******************************************************************\

Function: goto_rw

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_rw(const code_assignt &assign,
             std::list<exprt> &read, std::list<exprt> &write)
{
  get_objects_rec(LHS_W, assign.lhs(), read, write);
  get_objects_rec(READ, assign.rhs(), read, write);
}

/*******************************************************************\

Function: goto_rw

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_rw(const code_function_callt &function_call,
             std::list<exprt> &read, std::list<exprt> &write)
{
  if(function_call.lhs().is_not_nil())
    get_objects_rec(LHS_W, function_call.lhs(), read, write);

  get_objects_rec(READ, function_call.function(), read, write);

  forall_expr(it, function_call.arguments())
    get_objects_rec(READ, *it, read, write);
}

/*******************************************************************\

Function: goto_rw

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_rw(const goto_programt::instructiont &instruction,
             std::list<exprt> &read,
             std::list<exprt> &write)
{
  switch(instruction.type)
  {
  case NO_INSTRUCTION_TYPE:
    assert(false);
    break;
    
  case GOTO:
  case ASSUME:
  case ASSERT:
    get_objects_rec(READ, instruction.guard, read, write);
    break;
    
  case RETURN:
    {
      const code_returnt &code_return=to_code_return(instruction.code);
      if(code_return.has_return_value())
        get_objects_rec(READ, code_return.return_value(), read, write);
    }
    break;
    
  case OTHER:
    // don't know
    break;
    
  case DEAD:
  case SKIP:
  case START_THREAD:
  case END_THREAD:
  case LOCATION:
  case END_FUNCTION:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
  case THROW:
  case CATCH:
    // these don't read or write anything
    break;      

  case ASSIGN:
    goto_rw(to_code_assign(instruction.code), read, write);
    break;
  
  case DECL:
    get_objects_rec(LHS_W, to_code_decl(instruction.code).symbol(),
                    read, write);
    break;
  
  case FUNCTION_CALL:
    goto_rw(to_code_function_call(instruction.code), read, write);
    break;
  }
}

