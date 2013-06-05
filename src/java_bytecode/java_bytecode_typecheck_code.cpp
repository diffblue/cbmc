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
  
  // do operands, possibly recursive
  Forall_operands(it, code)
    typecheck_expr(*it);
}

