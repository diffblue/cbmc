/*******************************************************************\

Module: C++ Parser

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Parser

#include "cpp_parser.h"

bool cpp_parse(cpp_parsert &);

cpp_parsert::cpp_parsert(message_handlert &message_handler)
  : 
    parsert(message_handler),
    ansi_c_parser(message_handler),
    mode(configt::ansi_ct::flavourt::ANSI),
    recognize_wchar_t(true),
    token_buffer(ansi_c_parser),
    asm_block_following(false)
{
}


bool cpp_parsert::parse()
{
  ansi_c_parser.cpp98=true;
  ansi_c_parser.cpp11=
    config.cpp.cpp_standard==configt::cppt::cpp_standardt::CPP11 ||
    config.cpp.cpp_standard==configt::cppt::cpp_standardt::CPP14;
  ansi_c_parser.ts_18661_3_Floatn_types=false;
  ansi_c_parser.Float128_type = false;
  ansi_c_parser.in=in;
  ansi_c_parser.mode=mode;
  ansi_c_parser.set_file(get_file());
  return cpp_parse(*this);
}
