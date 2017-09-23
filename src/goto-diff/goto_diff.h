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

class goto_difft:public messaget
{
public:
  explicit goto_difft(
    const goto_modelt &_goto_model1,
    const goto_modelt &_goto_model2,
    message_handlert &_message_handler
    )
    :
    messaget(_message_handler),
    goto_model1(_goto_model1),
    goto_model2(_goto_model2),
    ui(ui_message_handlert::uit::PLAIN),
    total_functions_count(0)
     {}

  virtual bool operator()()=0;

  void set_ui(ui_message_handlert::uit _ui) { ui=_ui; }

  virtual std::ostream &output_functions(std::ostream &out) const;

protected:
  const goto_modelt &goto_model1;
  const goto_modelt &goto_model2;
  ui_message_handlert::uit ui;

  unsigned total_functions_count;
  using irep_id_sett = std::set<irep_idt>;
  irep_id_sett new_functions, modified_functions, deleted_functions;

  void convert_function_group(
    json_arrayt &result,
    const irep_id_sett &function_group) const;
  void convert_function(
    json_objectt &result,
    const irep_idt &function_name) const;
};

#endif // CPROVER_GOTO_DIFF_GOTO_DIFF_H
