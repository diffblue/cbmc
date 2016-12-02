/*******************************************************************\

Module: Obtain a Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GET_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_GET_GOTO_MODEL_H

#include <util/message.h>

#include "goto_model.h"

class get_goto_modelt:public goto_modelt, public messaget
{
public:
  bool operator()(const std::vector<std::string> &);
};

#endif // CPROVER_GOTO_PROGRAMS_GET_GOTO_MODEL_H
