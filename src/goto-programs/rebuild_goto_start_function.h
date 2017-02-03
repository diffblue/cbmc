/*******************************************************************\
 Module: Goto Programs
 Author: Thomas Kiley, thomas@diffblue.com
\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_REBUILD_GOTO_START_FUNCTION_H
#define CPROVER_GOTO_PROGRAMS_REBUILD_GOTO_START_FUNCTION_H

#include <util/message.h>
#include <util/symbol_table.h>
#include <goto-programs/goto_functions.h>

#define OPT_FUNCTIONS \
  "(function):"

#define HELP_FUNCTIONS \
  " --function name              set main function name\n"

class rebuild_goto_start_functiont: public messaget
{
public:
  rebuild_goto_start_functiont(
    message_handlert &_message_handler,
    symbol_tablet &symbol_table,
    goto_functionst &goto_functions);

  bool operator()(const irep_idt &entry_function);

private:
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;
};

#endif // CPROVER_GOTO_PROGRAMS_REBUILD_GOTO_START_FUNCTION_H
