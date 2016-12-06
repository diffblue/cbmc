#include <fstream>

#include <util/config.h>

#include <cpp/cpp_parser.h>

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int main(int argc, const char *argv[])
{
  if(argc!=2) return 1;

  config.ansi_c.set_ILP32();

  std::ifstream in(argv[1]);
  cpp_parser.in=&in;

  cpp_parser.parse();

  return 0;
}
