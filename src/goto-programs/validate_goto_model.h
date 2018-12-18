/*******************************************************************\

Module: Validate Goto Programs

Author: Diffblue

Date: Oct 2018

\*******************************************************************/
#ifndef CPROVER_GOTO_PROGRAMS_VALIDATE_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_VALIDATE_GOTO_MODEL_H

#include <util/validate.h>

struct goto_model_validation_optionst
{
  bool entry_point_exists;
  bool function_pointer_calls_removed;
  bool check_returns_removed;
  bool check_called_functions;
  bool check_last_instruction;
  bool check_sourcecode_location;

  goto_model_validation_optionst()
    : entry_point_exists{true},
      function_pointer_calls_removed{false},
      check_returns_removed{false},
      check_called_functions{false},
      check_last_instruction{false},
      check_sourcecode_location{false}
  {
  }

  goto_model_validation_optionst(bool options_value)
    : entry_point_exists{options_value},
      function_pointer_calls_removed{options_value},
      check_returns_removed{options_value},
      check_called_functions{options_value},
      check_last_instruction{options_value},
      check_sourcecode_location{options_value}
  {
  }
};

class goto_functionst;

void validate_goto_model(
  const goto_functionst &goto_functions,
  const validation_modet vm,
  const goto_model_validation_optionst validation_options);

#endif // CPROVER_GOTO_PROGRAMS_VALIDATE_GOTO_MODEL_H
