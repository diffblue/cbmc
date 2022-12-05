/*******************************************************************\

Module: Loop IDs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Loop IDs

#ifndef CPROVER_GOTO_PROGRAMS_LOOP_IDS_H
#define CPROVER_GOTO_PROGRAMS_LOOP_IDS_H

#include <util/ui_message.h>

class goto_functionst;
class goto_modelt;
class goto_programt;

/// Loop id used to identify loops. It consists of two arguments:
/// `function_id`
///     the function id stored as keys of `function_mapt`; and
/// `loop_number`
///     the index of loop indicated by `loop_number` of backward
///     goto instruction.
struct loop_idt
{
  loop_idt(const irep_idt &function_id, const unsigned int loop_number)
    : function_id(function_id), loop_number(loop_number)
  {
  }

  loop_idt() : function_id(""), loop_number()
  {
  }

  loop_idt(const loop_idt &other)
    : function_id(other.function_id), loop_number(other.loop_number)
  {
  }

  irep_idt function_id;
  optionalt<unsigned int> loop_number;

  bool operator==(const loop_idt &o) const
  {
    return function_id == o.function_id && loop_number == o.loop_number;
  }

  bool operator!=(const loop_idt &o) const
  {
    return !operator==(o);
  }

  bool operator<(const loop_idt &o) const
  {
    return function_id < o.function_id ||
           (function_id == o.function_id && loop_number < o.loop_number);
  }
};

void show_loop_ids(
  ui_message_handlert::uit,
  const goto_modelt &);

void show_loop_ids(
  ui_message_handlert::uit,
  const goto_functionst &);

void show_loop_ids(
  ui_message_handlert::uit,
  const irep_idt &function_id,
  const goto_programt &);

#endif // CPROVER_GOTO_PROGRAMS_LOOP_IDS_H
