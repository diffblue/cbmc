/*******************************************************************\

Module: Obtain a Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GET_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_GET_GOTO_MODEL_H

#include <util/message.h>
#include <util/cmdline.h>

#include "goto_model.h"

class get_goto_modelt:public goto_modelt, public messaget
{
public:
  get_goto_modelt() : generate_start_function(true) {}
  bool operator()(const cmdlinet &);
  bool generate_start_function;
};

#endif // CPROVER_GOTO_PROGRAMS_GET_GOTO_MODEL_H
