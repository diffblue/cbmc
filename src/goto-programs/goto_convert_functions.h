/*******************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_GOTO_CONVERT_FUNCTIONS_H
#define CPROVER_GOTO_CONVERT_FUNCTIONS_H

#include "goto_functions.h"
#include "goto_convert_class.h"

// convert it all!
void goto_convert(
  contextt &context,
  goto_functionst &functions,
  message_handlert &message_handler);
  
// just convert a specific function
void goto_convert(
  const irep_idt &identifier,
  contextt &context,
  goto_functionst &functions,
  message_handlert &message_handler);
  
class goto_convert_functionst:public goto_convertt
{
public:
  void goto_convert();
  void convert_function(const irep_idt &identifier);

  goto_convert_functionst(
    contextt &_context,
    goto_functionst &_functions,
    message_handlert &_message_handler);
  
  virtual ~goto_convert_functionst();

protected:
  goto_functionst &functions;
  
  static bool hide(const goto_programt &goto_program);

  //
  // function calls  
  //
  void add_return(
    goto_functionst::goto_functiont &f,
    const locationt &location);
};

#endif
