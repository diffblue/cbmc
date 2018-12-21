/*******************************************************************\

Module: Goto Programs

Author: Thomas Kiley, thomas@diffblue.com

\*******************************************************************/

/// \file
/// Goto Programs Author: Thomas Kiley, thomas@diffblue.com

#ifndef CPROVER_GOTO_PROGRAMS_REBUILD_GOTO_START_FUNCTION_H
#define CPROVER_GOTO_PROGRAMS_REBUILD_GOTO_START_FUNCTION_H

#include <util/message.h>
class optionst;

#include "lazy_goto_model.h"


class symbol_tablet;
class goto_functionst;

#define OPT_FUNCTIONS \
  "(function):"

#define HELP_FUNCTIONS \
  " --function name              set main function name\n"

template<typename maybe_lazy_goto_modelt>
class rebuild_goto_start_function_baset: public messaget
{
public:
  rebuild_goto_start_function_baset(
    const optionst &options,
    maybe_lazy_goto_modelt &goto_model,
    message_handlert &message_handler);

  bool operator()();

private:
  irep_idt get_entry_point_mode() const;

  void remove_existing_entry_point();

  const optionst &options;
  maybe_lazy_goto_modelt &goto_model;
};

// NOLINTNEXTLINE(readability/namespace)  using required for templates
using rebuild_goto_start_functiont =
  rebuild_goto_start_function_baset<goto_modelt>;

// NOLINTNEXTLINE(readability/namespace)  using required for templates
using rebuild_lazy_goto_start_functiont =
  rebuild_goto_start_function_baset<lazy_goto_modelt>;

#endif // CPROVER_GOTO_PROGRAMS_REBUILD_GOTO_START_FUNCTION_H
