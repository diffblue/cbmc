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
	  goto_modelt &_goto_model,
	  const optionst &_options,
	  message_handlert &_message_handler,
	  const bool &_constant_propagation):
	  ai_analysist(_goto_model,_options,_message_handler,
			  _constant_propagation)
    {
    }
	void simplify_guards(const bool constant_propagation);
};

#endif
