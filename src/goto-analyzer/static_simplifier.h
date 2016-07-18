/*******************************************************************\

Module:

Author: Lucas Cordeiro, lucas.cordeiro@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_STATIC_SIMPLIFIER_H
#define CPROVER_STATIC_SIMPLIFIER_H

#include "ai_analysis.h"

class static_simplifiert: public ai_analysist
{
  public:
	static_simplifiert(
	  const goto_modelt &_goto_model,
	  const optionst &_options,
	  message_handlert &_message_handler):
	  ai_analysist(_goto_model,_options,_message_handler)
    {
    }
};

#endif
