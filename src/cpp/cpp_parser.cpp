/*******************************************************************\

Module: C++ Parser

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Parser

#include "cpp_parser.h"

#include <util/config.h>

cpp_parsert cpp_parser;

bool cpp_parse();

bool cpp_parsert::parse()
{
  // We use the ANSI-C scanner
  ansi_c_parser.cpp98=true;
  ansi_c_parser.cpp11 =
    config.cpp.cpp_standard == configt::cppt::cpp_standardt::CPP11 ||
    config.cpp.cpp_standard == configt::cppt::cpp_standardt::CPP14 ||
    config.cpp.cpp_standard == configt::cppt::cpp_standardt::CPP17;
  ansi_c_parser.ts_18661_3_Floatn_types=false;
  ansi_c_parser.in=in;
  ansi_c_parser.mode=mode;
  ansi_c_parser.set_file(get_file());
  ansi_c_parser.set_message_handler(get_message_handler());

  return cpp_parse();
}
