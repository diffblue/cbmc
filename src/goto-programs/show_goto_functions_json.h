/*******************************************************************\

Module: Goto Program

Author: Thomas Kiley

\*******************************************************************/

/// \file
/// Goto Program

#ifndef CPROVER_GOTO_PROGRAMS_SHOW_GOTO_FUNCTIONS_JSON_H
#define CPROVER_GOTO_PROGRAMS_SHOW_GOTO_FUNCTIONS_JSON_H

#include <util/json.h>

class goto_functionst;

class show_goto_functions_jsont
{
public:
  explicit show_goto_functions_jsont(
    bool _list_only = false);

  json_objectt convert(const goto_functionst &goto_functions);
  void operator()(
    const goto_functionst &goto_functions, std::ostream &out, bool append=true);

private:
  bool list_only;
};

#endif // CPROVER_GOTO_PROGRAMS_SHOW_GOTO_FUNCTIONS_JSON_H
