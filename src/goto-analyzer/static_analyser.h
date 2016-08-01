/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_STATIC_ANALYSER_H
#define CPROVER_STATIC_ANALYSER_H

#include "ai_analysis.h"

class static_analysert: public ai_analysist
{
  public:
	static_analysert(
	  goto_modelt &_goto_model,
	  const optionst &_options,
	  message_handlert &_message_handler,
	  const bool &_constant_propagation):
	  ai_analysist(_goto_model,_options,_message_handler,
			  _constant_propagation)
    {
    }

	//output
    void show_intervals(
      const goto_modelt &,
      std::ostream &);

};
#endif
