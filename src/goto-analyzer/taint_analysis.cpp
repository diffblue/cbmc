/*******************************************************************\

Module: Taint Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "taint_analysis.h"
#include "taint_parser.h"

/*******************************************************************\

   Class: taint_analysist

 Purpose:

\*******************************************************************/

class taint_analysist:public messaget
{
public:
  taint_analysist(
    const namespacet &_ns):
    ns(_ns)
  {
  }

  bool operator()(
    const std::string &taint_file_name,
    goto_functionst &goto_functions);

protected:
  const namespacet &ns;
  taint_parse_treet taint;
  
  void instrument(goto_functionst &);
  void instrument(goto_functionst::goto_functiont &);
};

/*******************************************************************\

Function: taint_analysist::instrument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void taint_analysist::instrument(goto_functionst &goto_functions)
{
  for(auto & function : goto_functions.function_map)
    instrument(function.second);
}

/*******************************************************************\

Function: taint_analysist::instrument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void taint_analysist::instrument(
  goto_functionst::goto_functiont &goto_function)
{
}

/*******************************************************************\

Function: taint_analysist::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool taint_analysist::operator()(
  const std::string &taint_file_name,
  goto_functionst &goto_functions)
{
  status() << "Reading taint file `" << taint_file_name
           << "'" << eom;

  if(taint_parser(taint_file_name, taint, get_message_handler()))
  {
    error() << "Failed to read taint definition file" << eom;
    return true;
  }

  status() << "Got " << taint.entries.size()
           << " taint definitions" << eom;

  taint.output(debug());
  debug() << eom;

  instrument(goto_functions);

  return false;
}

/*******************************************************************\

Function: taint_analysis

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool taint_analysis(
  goto_functionst &goto_functions,
  const namespacet &ns,
  const std::string &taint_file_name,
  message_handlert &message_handler)
{
  taint_analysist taint_analysis(ns);
  taint_analysis.set_message_handler(message_handler);
  return taint_analysis(taint_file_name, goto_functions);
}

