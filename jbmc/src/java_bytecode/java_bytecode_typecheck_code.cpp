/*******************************************************************\

Module: JAVA Bytecode Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Conversion / Type Checking

#include "java_bytecode_typecheck.h"

#include <util/goto_instruction_code.h>
#include <util/std_code.h>

void java_bytecode_typecheckt::typecheck_code(codet &code)
{
  const irep_idt &statement=code.get_statement();

  if(statement==ID_assign)
  {
    code_frontend_assignt &code_assign = to_code_frontend_assign(code);
    typecheck_expr(code_assign.lhs());
    typecheck_expr(code_assign.rhs());

    code_assign.rhs() = typecast_exprt::conditional_cast(
      code_assign.rhs(), code_assign.lhs().type());
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
    if(code_ifthenelse.else_case().is_not_nil())
      typecheck_code(code_ifthenelse.else_case());
  }
  else if(statement==ID_switch)
  {
    code_switcht &code_switch = to_code_switch(code);
    typecheck_expr(code_switch.value());
  }
  else if(statement==ID_return)
  {
    code_returnt &code_return = to_code_return(code);
    typecheck_expr(code_return.return_value());
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
  else if(statement==ID_assert || statement==ID_assume)
  {
    typecheck_expr(code.op0());
  }
}
