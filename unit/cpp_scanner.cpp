/*******************************************************************\

Module: CPP lexer test

Author: Daniel Kroening, 2015

\*******************************************************************/

#include <fstream>
#include <iostream>

#include <util/config.h>
#include <ansi-c/ansi_c_parser.h>

#include <cpp/cpp_parser.h>
#include <cpp/cpp_token_buffer.h>

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

  config.ansi_c.set_ILP32();

  ansi_c_scanner_init();
  ansi_c_parser.clear();
  ansi_c_parser.mode=ansi_c_parsert::GCC;
  ansi_c_parser.cpp98=true;
  ansi_c_parser.cpp11=false;
  ansi_c_parser.ts_18661_3_Floatn_types = false;
  ansi_c_parser.__float128_is_keyword = false;
  ansi_c_parser.float16_type = false;
  ansi_c_parser.bf16_type = false;
  ansi_c_parser.fp16_type = false;
  ansi_c_parser.in=&in;
  cpp_parser.in=&in;

  cpp_tokent tk;

  while(cpp_parser.token_buffer.get_token(tk))
    std::cout << tk.text << '\n';

  return 0;
}
