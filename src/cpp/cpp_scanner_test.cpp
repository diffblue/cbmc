#include <fstream>
#include <iostream>

#include <ansi-c/ansi_c_parser.h>

#include "cpp_parser.h"
#include "cpp_token_buffer.h"

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

  ansi_c_parser.cpp98=true;
  ansi_c_parser.cpp11=false;
  ansi_c_parser.in=&in;
  cpp_parser.in=&in;

  cpp_tokent tk;
  
  while(cpp_parser.token_buffer.GetToken(tk))
    std::cout << tk.text << '\n';
}

