/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "json_parser.h"

#include <fstream>

int yyjsonlex_init_extra(json_parsert *, void **);
int yyjsonlex_destroy(void *);
int yyjsonparse(json_parsert &, void *);

bool json_parsert::parse()
{
  void *scanner;
  yyjsonlex_init_extra(this, &scanner);
  bool parse_fail = yyjsonparse(*this, scanner) != 0;
  yyjsonlex_destroy(scanner);
  return parse_fail;
}

// 'do it all' function
bool parse_json(
  std::istream &in,
  const std::string &filename,
  message_handlert &message_handler,
  jsont &dest)
{
  json_parsert json_parser{message_handler};

  json_parser.set_file(filename);
  json_parser.in=&in;

  bool result=json_parser.parse();

  // save result
  if(json_parser.stack.size()==1)
    dest.swap(json_parser.stack.top());

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
