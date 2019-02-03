/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "json_parser.h"

#include <fstream>

void json_parser_init(json_parsert *json_parser);
void json_scanner_init(json_parsert *json_parser);
int yyjsonparse();
void yyjsonrestart(FILE *input_file);

int yyjsonerror(const std::string &error);

bool json_parsert::parse()
{
  json_scanner_init(this);
  json_parser_init(this);
  return yyjsonparse()!=0;
}

void json_parsert::clear()
{
  stack=stackt();
  yyjsonrestart(nullptr);
  json_parser_init(nullptr);
  json_scanner_init(nullptr);
}

// 'do it all' function
bool parse_json(
  std::istream &in,
  const std::string &filename,
  message_handlert &message_handler,
  jsont &dest)
{
  json_parsert json_parser(message_handler);
  json_parser.set_file(filename);
  json_parser.in=&in;

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
