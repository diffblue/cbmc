/*******************************************************************\

Module: GOTO-DIFF Languages

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_GOTO_DIFF_LANGUAGES_H
#define CPROVER_GOTO_DIFF_LANGUAGES_H

#include <langapi/language_ui.h>
#include <goto-programs/goto_model.h>

class goto_diff_languagest :
  public language_uit
{
public:
  explicit goto_diff_languagest(const std::string& tool, 
                                const cmdlinet& cmdline) :
  language_uit(tool, cmdline)
  {
    register_languages();
  }

protected:
  virtual void register_languages();

};

#endif
