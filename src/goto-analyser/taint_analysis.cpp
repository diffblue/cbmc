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

bool taint_analysis(
  const goto_functionst &goto_functions,
  const namespacet &ns,
  const std::string &taint_file_name,
  message_handlert &message_handler)
{
  taint_parse_treet taint;

  if(taint_parser(taint_file_name, taint, message_handler))
    return true;

  return false;
}

