#include <fstream>

#include "cpp_parser.h"

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int main(int argc, const char *argv[])
{
  if(argc!=2) return 1;

  std::ifstream in(argv[1]);
  cpp_parser.in=&in;
  
  cpp_parser.parse();
}

