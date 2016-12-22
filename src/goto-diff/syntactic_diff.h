/*******************************************************************\

Module: Syntactic GOTO-DIFF

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_GOTO_DIFF_SYNTACTIC_DIFF_H
#define CPROVER_GOTO_DIFF_SYNTACTIC_DIFF_H

#include "goto_diff.h"

class syntactic_difft:public goto_difft
{
 public:
  explicit syntactic_difft(
    const goto_modelt &_goto_model1,
    const goto_modelt &_goto_model2,
    message_handlert &_message_handler):
    goto_difft(_goto_model1, _goto_model2, _message_handler)
  {
  }

  virtual bool operator()();
};

#endif // CPROVER_GOTO_DIFF_SYNTACTIC_DIFF_H
