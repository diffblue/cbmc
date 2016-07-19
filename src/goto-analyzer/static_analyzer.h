/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_STATIC_ANALYZER_H
#define CPROVER_STATIC_ANALYZER_H

#include "ai_analysis.h"

class static_analyzert: public ai_analysist
{
  public:
	static_analyzert(
	  goto_modelt &_goto_model,
	  const optionst &_options,
	  message_handlert &_message_handler):
	  ai_analysist(_goto_model,_options,_message_handler)
    {
    }
};

#endif
