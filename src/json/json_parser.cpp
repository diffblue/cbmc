/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stdlib.h>
#include <string.h>

#include <fstream>

#include "json_parser.h"

json_parsert json_parser;

/*******************************************************************\

Function: parse_json

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

// 'do it all' function
bool parse_json(
  std::istream &in,
  const std::string &filename,
  message_handlert &message_handler,
  jsont &dest)
{
  json_parser.clear();
  json_parser.set_file(filename);
  json_parser.in=&in;
  json_parser.set_message_handler(message_handler);

  bool result=yyjsonparse()!=0;

  // save result
  if(json_parser.stack.size()==1)
    dest.swap(json_parser.stack.top());

  // save some memory
  json_parser.clear();

  return result;  
}

/*******************************************************************\

Function: parse_json

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

// 'do it all' function
bool parse_json(
  const std::string &filename,
  message_handlert &message_handler,
  jsont &dest)
{
  std::ifstream in(filename.c_str());
  
  if(!in) return true;
 
  return parse_json(in, filename, message_handler, dest);
}
