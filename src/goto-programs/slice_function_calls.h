/*******************************************************************\

Module: Slice Function Calls and Direct Dependency Parameters

Author: Matthias Güdemann, matthias.guedemann@diffblue.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_SLICE_FUNCTION_CALLS_H
#define CPROVER_GOTO_PROGRAMS_SLICE_FUNCTION_CALLS_H

#include "goto_model.h"

#include <string>

void slice_function_calls(goto_model_functiont &, const std::string &);

class slice_function_callst
{
  const std::string &slice_function;

public:
  slice_function_callst(const std::string &_slice_function)
    : slice_function(_slice_function)
  {
  }
  void operator()(goto_model_functiont &);
};

#endif // CPROVER_GOTO_PROGRAMS_SLICE_FUNCTION_CALLS_H
