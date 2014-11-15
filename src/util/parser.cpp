/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "parser.h"
#include "i2string.h"

#ifdef _WIN32
int isatty(int f)
{
  return 0;
}
#endif

/*******************************************************************\

Function: _newstack

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt &_newstack(parsert &parser, unsigned &x)
{
  x=(unsigned)parser.stack.size();

  if(x>=parser.stack.capacity())
    parser.stack.reserve(x*2);

  parser.stack.push_back(static_cast<const exprt &>(get_nil_irep()));
  return parser.stack.back();
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void parsert::parse_error(
  const std::string &message,
  const std::string &before)
{
  std::string tmp=message;
  if(before!="") tmp+=" before `"+before+"'";
  
  #if 0
  source_locationt tmp_source_location=source_location;
  tmp_source_location.set_column(column-before.size());
  print(1, tmp, -1, tmp_source_location);
  #else
  print(1, tmp, -1, source_location);
  #endif
}

