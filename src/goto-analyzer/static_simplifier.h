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
	  const bool &_constant_propagation,
	  const bool &_intervals):
	  ai_analysist(_goto_model,_options,_message_handler,
			  _constant_propagation, _intervals)
    {
    }
	void simplify_guards();
	bool write_goto_program(const std::string &filename);
};

#endif
