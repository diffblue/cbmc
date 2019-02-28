/*******************************************************************\
Module: Validate Goto Programs

Author: Diffblue

Date: Oct 2018

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_VALIDATE_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_VALIDATE_GOTO_MODEL_H

#include <util/validate.h>

class goto_model_validation_optionst final
{
public:
  // this check is disabled by default (not all goto programs
  // have an entry point)
  bool entry_point_exists = false;

  bool function_pointer_calls_removed = true;
  bool check_returns_removed = true;
  bool check_called_functions = true;

private:
  void set_all_flags(bool options_value)
  {
    entry_point_exists = options_value;
    function_pointer_calls_removed = options_value;
    check_returns_removed = options_value;
    check_called_functions = options_value;
  }

public:
  goto_model_validation_optionst() = default;

  enum class set_optionst
  {
    all_true,
    all_false
  };

  explicit goto_model_validation_optionst(set_optionst flag_option)
  {
    switch(flag_option)
    {
    case set_optionst::all_true:
      set_all_flags(true);
      break;
    case set_optionst::all_false:
      set_all_flags(false);
      break;
    }
  }
};

class goto_functionst;

void validate_goto_model(
  const goto_functionst &goto_functions,
  const validation_modet vm,
  const goto_model_validation_optionst validation_options);

#endif // CPROVER_GOTO_PROGRAMS_VALIDATE_GOTO_MODEL_H
