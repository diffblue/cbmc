/*******************************************************************\

Module: Goto Program Template

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "goto_program_template.h"

/*******************************************************************\

Function: operator<<

  Inputs:

 Outputs:

 Purpose: 
 
\*******************************************************************/

std::ostream &operator<<(std::ostream &out, goto_program_instruction_typet t)
{
  switch(t)
  {
  case NO_INSTRUCTION_TYPE: out << "NO_INSTRUCTION_TYPE"; break;
  case GOTO: out << "GOTO"; break;
  case ASSUME: out << "ASSUME"; break;
  case ASSERT: out << "ASSERT"; break;
  case OTHER: out << "OTHER"; break;
  case DECL: out << "DECL"; break;
  case DEAD: out << "DEAD"; break;
  case SKIP: out << "SKIP"; break;
  case START_THREAD: out << "START_THREAD"; break;
  case END_THREAD: out << "END_THREAD"; break;
  case LOCATION: out << "LOCATION"; break;
  case END_FUNCTION: out << "END_FUNCTION"; break;
  case ATOMIC_BEGIN: out << "ATOMIC_BEGIN"; break;
  case ATOMIC_END: out << "ATOMIC_END"; break;
  case RETURN: out << "RETURN"; break;
  case ASSIGN: out << "ASSIGN"; break;
  case FUNCTION_CALL: out << "FUNCTION_CALL"; break;
  default:
    out << "?";
  }
  
  return out;
}
