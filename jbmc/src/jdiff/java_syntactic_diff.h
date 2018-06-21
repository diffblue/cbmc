/*******************************************************************\

Module: Syntactic GOTO-DIFF for Java

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Syntactic GOTO-DIFF for Java

#ifndef CPROVER_JDIFF_JAVA_SYNTACTIC_DIFF_H
#define CPROVER_JDIFF_JAVA_SYNTACTIC_DIFF_H

#include <goto-diff/goto_diff.h>

class java_syntactic_difft : public goto_difft
{
public:
  java_syntactic_difft(
    const goto_modelt &_goto_model1,
    const goto_modelt &_goto_model2,
    const optionst &_options,
    ui_message_handlert &_message_handler)
    : goto_difft(_goto_model1, _goto_model2, _options, _message_handler)
  {
  }

  virtual bool operator()();
};

#endif // CPROVER_JDIFF_JAVA_SYNTACTIC_DIFF_H
