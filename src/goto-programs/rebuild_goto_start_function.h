/*******************************************************************\
 Module: Goto Programs
 Author: Thomas Kiley, thomas@diffblue.com
\*******************************************************************/

/// \file
/// Goto Programs Author: Thomas Kiley, thomas@diffblue.com

#ifndef CPROVER_GOTO_PROGRAMS_REBUILD_GOTO_START_FUNCTION_H
#define CPROVER_GOTO_PROGRAMS_REBUILD_GOTO_START_FUNCTION_H

#include <util/cmdline.h>
#include <util/message.h>

class symbol_tablet;
class goto_functionst;

#define OPT_FUNCTIONS \
  "(function):"

#define HELP_FUNCTIONS \
  " --function name              set main function name\n"

class rebuild_goto_start_functiont: public messaget
{
public:
  rebuild_goto_start_functiont(
    message_handlert &_message_handler,
    const cmdlinet &cmdline,
    symbol_tablet &symbol_table,
    goto_functionst &goto_functions);

  bool operator()(const irep_idt &entry_function);

private:
  irep_idt get_entry_point_mode() const;

  void remove_existing_entry_point();

  const cmdlinet &cmdline;
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;
};

#endif // CPROVER_GOTO_PROGRAMS_REBUILD_GOTO_START_FUNCTION_H
