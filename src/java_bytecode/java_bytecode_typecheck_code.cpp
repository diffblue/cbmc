/*******************************************************************\

Module: JAVA Bytecode Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#if 0
#include <util/std_types.h>
#include <util/prefix.h>
#include <util/config.h>

#include <ansi-c/expr2c.h>
#endif

#include "java_bytecode_typecheck.h"

/*******************************************************************\

Function: java_bytecode_typecheckt::typecheck_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_typecheckt::typecheck_code(codet &code)
{ 
  const irep_idt &statement=code.get_statement();
  
  if(statement==ID_assign)
  {
    code_assignt &code_assign=to_code_assign(code);
    typecheck_expr(code_assign.lhs());
    typecheck_expr(code_assign.rhs());
    
    if(code_assign.lhs().type()!=code_assign.rhs().type())
      code_assign.rhs().make_typecast(code_assign.lhs().type());
  }
  else if(statement==ID_block)
  {
    Forall_operands(it, code)
      typecheck_code(to_code(*it));
  }
  else if(statement==ID_label)
  {
    code_labelt &code_label=to_code_label(code);
    typecheck_code(code_label.code());
  }
  else if(statement==ID_goto)
  {
  }
  else if(statement==ID_ifthenelse)
  {
    code_ifthenelset &code_ifthenelse=to_code_ifthenelse(code);
    typecheck_expr(code_ifthenelse.cond());
    typecheck_code(code_ifthenelse.then_case());
  }
  else if(statement==ID_return)
  {
    if(code.operands().size()==1)
      typecheck_expr(code.op0());
  }
  else if(statement==ID_function_call)
  {
    code_function_callt &code_function_call=to_code_function_call(code);
    typecheck_expr(code_function_call.lhs());
    typecheck_expr(code_function_call.function());
    
    for(code_function_callt::argumentst::iterator
        a_it=code_function_call.arguments().begin();
        a_it!=code_function_call.arguments().end();
        a_it++)
      typecheck_expr(*a_it);
  }
}

