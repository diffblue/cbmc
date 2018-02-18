/*******************************************************************\

Module: GOTO-DIFF Base Class

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// GOTO-DIFF Base Class

#ifndef CPROVER_GOTO_DIFF_GOTO_DIFF_H
#define CPROVER_GOTO_DIFF_GOTO_DIFF_H

#include <goto-programs/goto_model.h>

#include <util/json.h>
#include <util/ui_message.h>

#include <ostream>

class optionst;

class goto_difft:public messaget
{
public:
  goto_difft(
    const goto_modelt &_goto_model1,
    const goto_modelt &_goto_model2,
    const optionst &_options,
    message_handlert &_message_handler)
    : messaget(_message_handler),
      goto_model1(_goto_model1),
      goto_model2(_goto_model2),
      options(_options),
      ui(ui_message_handlert::uit::PLAIN),
      total_functions_count(0)
  {
  }

  virtual bool operator()()=0;

  void set_ui(ui_message_handlert::uit _ui) { ui=_ui; }

  virtual void output_functions() const;

protected:
  const goto_modelt &goto_model1;
  const goto_modelt &goto_model2;
  const optionst &options;
  ui_message_handlert::uit ui;

  unsigned total_functions_count;
  typedef std::set<irep_idt> irep_id_sett;
  irep_id_sett new_functions, modified_functions, deleted_functions;

  void output_function_group(
    const std::string &group_name,
    const irep_id_sett &function_group,
    const goto_modelt &goto_model) const;
  void output_function(
    const irep_idt &function_name,
    const goto_modelt &goto_model) const;

  void convert_function_group_json(
    json_arrayt &result,
    const irep_id_sett &function_group,
    const goto_modelt &goto_model) const;
  void convert_function_json(
    json_objectt &result,
    const irep_idt &function_name,
    const goto_modelt &goto_model) const;
};

#endif // CPROVER_GOTO_DIFF_GOTO_DIFF_H
