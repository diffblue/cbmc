/*******************************************************************\

Module: GOTO-DIFF Base Class

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// GOTO-DIFF Base Class

#ifndef CPROVER_GOTO_DIFF_GOTO_DIFF_H
#define CPROVER_GOTO_DIFF_GOTO_DIFF_H

#include <util/ui_message.h>

#include <iosfwd>
#include <set>

class goto_modelt;
class json_arrayt;
class json_objectt;
class optionst;

class goto_difft
{
public:
  goto_difft(
    const goto_modelt &_goto_model1,
    const goto_modelt &_goto_model2,
    const optionst &_options,
    ui_message_handlert &_message_handler)
    : message_handler(_message_handler),
      goto_model1(_goto_model1),
      goto_model2(_goto_model2),
      options(_options),
      total_functions_count(0)
  {
  }

  virtual bool operator()()=0;

  virtual void output_functions() const;

protected:
  ui_message_handlert &message_handler;
  const goto_modelt &goto_model1;
  const goto_modelt &goto_model2;
  const optionst &options;

  unsigned total_functions_count;
  std::set<irep_idt> new_functions, modified_functions, deleted_functions;

  void output_function_group(
    const std::string &group_name,
    const std::set<irep_idt> &function_group,
    const goto_modelt &goto_model) const;
  void output_function(
    const irep_idt &function_name,
    const goto_modelt &goto_model) const;

  void convert_function_group_json(
    json_arrayt &result,
    const std::set<irep_idt> &function_group,
    const goto_modelt &goto_model) const;
  void convert_function_json(
    json_objectt &result,
    const irep_idt &function_name,
    const goto_modelt &goto_model) const;
};

#endif // CPROVER_GOTO_DIFF_GOTO_DIFF_H
