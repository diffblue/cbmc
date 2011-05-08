/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "std_code.h"
#include "std_expr.h"

/*******************************************************************\

Function: code_declt::get_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const irep_idt &code_declt::get_identifier() const
{
  return to_symbol_expr(symbol()).get_identifier();
}

/*******************************************************************\

Function: codet::make_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

code_blockt &codet::make_block()
{
  if(get_statement()==ID_block)
    return static_cast<code_blockt &>(*this);

  exprt tmp;
  tmp.swap(*this);

  *this=codet();
  set_statement(ID_block);
  move_to_operands(tmp);
  
  return static_cast<code_blockt &>(*this);
}

/*******************************************************************\

Function: codet::first_statement

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

codet &codet::first_statement()
{
  const irep_idt &statement=get_statement();

  if(has_operands())
  {
    if(statement==ID_block)
      return to_code(op0()).first_statement();
    else if(statement==ID_label)
      return to_code(op0()).first_statement();
  }

  return *this;
}

/*******************************************************************\

Function: first_statement

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const codet &codet::first_statement() const
{
  const irep_idt &statement=get_statement();

  if(has_operands())
  {
    if(statement==ID_block)
      return to_code(op0()).first_statement();
    else if(statement==ID_label)
      return to_code(op0()).first_statement();
  }

  return *this;
}

/*******************************************************************\

Function: codet::last_statement

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

codet &codet::last_statement()
{
  const irep_idt &statement=get_statement();

  if(has_operands())
  {
    if(statement==ID_block)
      return to_code(operands().back()).last_statement();
    else if(statement==ID_label)
      return to_code(operands().back()).last_statement();
  }

  return *this;
}

/*******************************************************************\

Function: codet::last_statement

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const codet &codet::last_statement() const
{
  const irep_idt &statement=get_statement();

  if(has_operands())
  {
    if(statement==ID_block)
      return to_code(operands().back()).last_statement();
    else if(statement==ID_label)
      return to_code(operands().back()).last_statement();
  }

  return *this;
}
