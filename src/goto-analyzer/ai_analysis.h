/*******************************************************************\

Module: 

Author: Lucas Cordeiro, lucas.cordeiro@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_AI_ANALYSIS_H
#define CPROVER_AI_ANALYSIS_H

#include <fstream>

#include <util/message.h>
#include <util/namespace.h>
#include <util/options.h>

#include <util/json.h>
#include <util/xml.h>

#include <analyses/interval_domain.h>
#include <analyses/constant_propagator.h>

class ai_analysist:public messaget {

  public:
    ai_analysist(
	  goto_modelt &_goto_model,
	  const optionst &_options,
	  message_handlert &_message_handler,
	  const bool &_constant_propagation,
	  const bool &_intervals):
	  messaget(_message_handler),
	  symbol_table(_goto_model.symbol_table),
	  goto_functions(_goto_model.goto_functions),
	  ns(_goto_model.symbol_table),
	  options(_options),
	  constant_propagation(_constant_propagation),
	  intervals(_intervals)
	  {
	  }

	virtual ~ai_analysist()
	{
	}

  protected:
	symbol_tablet &symbol_table;
    goto_functionst &goto_functions;
    const namespacet ns;
    const optionst &options;
    const bool &constant_propagation;
    const bool &intervals;

    // analyses
    ait<interval_domaint> interval_analysis;

    void propagate_constants();

    tvt eval(goto_programt::const_targett);
};

#endif
