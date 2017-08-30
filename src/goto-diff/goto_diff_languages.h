/*******************************************************************\

Module: GOTO-DIFF Languages

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// GOTO-DIFF Languages

#ifndef CPROVER_GOTO_DIFF_GOTO_DIFF_LANGUAGES_H
#define CPROVER_GOTO_DIFF_GOTO_DIFF_LANGUAGES_H

#include <langapi/language_ui.h>
#include <goto-programs/goto_model.h>

class goto_diff_languagest:public language_uit
{
public:
  explicit goto_diff_languagest(
    const cmdlinet &cmdline,
    ui_message_handlert &ui_message_handler) :
  language_uit(cmdline, ui_message_handler)
  {
    register_languages();
  }

protected:
  virtual void register_languages();
};

#endif // CPROVER_GOTO_DIFF_GOTO_DIFF_LANGUAGES_H
