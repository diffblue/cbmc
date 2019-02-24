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
  bool entry_point_exists;
  bool function_pointer_calls_removed;
  bool check_returns_removed;
  bool check_called_functions;
  bool check_source_location;

private:
  void set_all_flags(bool options_value)
  {
    // temporarily disabled until adjustments made for regression tests that
    // have no entry point(e.g. testing json-ui warnings when there
    // is no entry point)
    entry_point_exists = false;
    function_pointer_calls_removed = options_value;
    check_returns_removed = options_value;
    check_called_functions = options_value;

    // this option is temporarily disabled until all source locations
    // are reliably set correctly
    check_source_location = false;
  }

public:
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
