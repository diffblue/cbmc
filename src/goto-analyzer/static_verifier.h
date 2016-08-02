/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_STATIC_ANALYZER_H
#define CPROVER_STATIC_ANALYZER_H

#include "ai_analysis.h"

class static_verifiert: public ai_analysist
{
  public:
	static_verifiert(
	  goto_modelt &_goto_model,
	  const optionst &_options,
	  message_handlert &_message_handler,
	  const bool &_constant_propagation,
	  const bool &_intervals):
	  ai_analysist(_goto_model,_options,_message_handler,
			  _constant_propagation, _intervals)
    {
    }

	bool operator()();

  private:

	//all available report types
    void plain_text_report();
    void json_report(const std::string &);
    void xml_report(const std::string &);

};
#endif
