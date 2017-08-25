/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "json_parser.h"

#include <fstream>

json_parsert json_parser;

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

  bool result=json_parser.parse();

  // save result
  if(json_parser.stack.size()==1)
    dest.swap(json_parser.stack.top());

  // save some memory
  json_parser.clear();

  return result;
}

// 'do it all' function
bool parse_json(
  const std::string &filename,
  message_handlert &message_handler,
  jsont &dest)
{
  std::ifstream in(filename);

  if(!in)
    return true;

  return parse_json(in, filename, message_handler, dest);
}
