/*******************************************************************\

Module: C++ Parser

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include "cpp_parser.h"

cpp_parsert cpp_parser;

/*******************************************************************\

Function: cpp_parsert::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cpp_parse();

bool cpp_parsert::parse()
{
  return cpp_parse();
}

/*******************************************************************\

Function: yycpperror

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

extern char *yycpptext;

int yycpperror(const std::string &error)
{
  cpp_parser.parse_error(error, yycpptext);
  return error.size()+1;
}
