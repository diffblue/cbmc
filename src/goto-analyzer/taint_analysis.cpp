/*******************************************************************\

Module: Taint Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "taint_analysis.h"
#include "taint_parser.h"

/*******************************************************************\

Function: taint_analysis

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#include <iostream>

bool taint_analysis(
  const goto_functionst &goto_functions,
  const namespacet &ns,
  const std::string &taint_file_name,
  message_handlert &message_handler)
{
  taint_parse_treet taint;
  
  messaget message(message_handler);
  
  message.status() << "Reading taint file `" << taint_file_name
                   << "'" << messaget::eom;

  if(taint_parser(taint_file_name, taint, message_handler))
  {
    message.error() << "Failed to read taint definition file"
                    << messaget::eom;
    return true;
  }

  message.status() << "Got " << taint.entries.size()
                   << " taint definitions" << messaget::eom;

  taint.output(std::cout);

  return false;
}

