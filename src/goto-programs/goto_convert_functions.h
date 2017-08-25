/*******************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

/// \file
/// Goto Programs with Functions

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_CONVERT_FUNCTIONS_H
#define CPROVER_GOTO_PROGRAMS_GOTO_CONVERT_FUNCTIONS_H

#include "goto_model.h"
#include "goto_convert_class.h"

// convert it all!
void goto_convert(
  symbol_tablet &symbol_table,
  goto_functionst &functions,
  message_handlert &);

// confusing, will go away
void goto_convert(
  symbol_tablet &symbol_table,
  goto_modelt &dest,
  message_handlert &);

// convert it all!
void goto_convert(
  goto_modelt &,
  message_handlert &);

// just convert a specific function
void goto_convert(
  const irep_idt &identifier,
  symbol_tablet &symbol_table,
  goto_functionst &functions,
  message_handlert &);

class goto_convert_functionst:public goto_convertt
{
public:
  void goto_convert();
  void convert_function(const irep_idt &identifier);

  goto_convert_functionst(
    symbol_tablet &_symbol_table,
    goto_functionst &_functions,
    message_handlert &_message_handler);

  virtual ~goto_convert_functionst();

protected:
  goto_functionst &functions;

  static bool hide(const goto_programt &);

  //
  // function calls
  //
  void add_return(
    goto_functionst::goto_functiont &,
    const source_locationt &);
};

#endif // CPROVER_GOTO_PROGRAMS_GOTO_CONVERT_FUNCTIONS_H
