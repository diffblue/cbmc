/*******************************************************************\

Module: C++ Parser

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <util/config.h>

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
  // We use the ANSI-C scanner
  ansi_c_parser.cpp98=true;
  ansi_c_parser.cpp11=config.ansi_c.cpp11;
  ansi_c_parser.in=in;
  ansi_c_parser.mode=mode;
  ansi_c_parser.set_file(get_file());
  ansi_c_parser.set_message_handler(get_message_handler());

  return cpp_parse();
}

