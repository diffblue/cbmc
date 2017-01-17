/*******************************************************************\

Module: Goto Program

Author: Thomas Kiley

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_SHOW_GOTO_FUNCTIONS_JSON_H
#define CPROVER_GOTO_PROGRAMS_SHOW_GOTO_FUNCTIONS_JSON_H

class goto_functionst;
class namespacet;

class show_goto_functions_jsont
{
public:
  explicit show_goto_functions_jsont(const namespacet &ns);

  void show_goto_functions(const goto_functionst &goto_functions);

private:
  const namespacet &ns;
};

#endif // CPROVER_GOTO_PROGRAMS_SHOW_GOTO_FUNCTIONS_JSON_H
