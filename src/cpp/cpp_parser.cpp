/*******************************************************************\

Module: C++ Parser

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Parser

#include "cpp_parser.h"

bool cpp_parse(cpp_parsert &, message_handlert &);

bool cpp_parsert::parse()
{
  token_buffer.ansi_c_parser.in = in;
  token_buffer.ansi_c_parser.mode = mode;
  token_buffer.ansi_c_parser.set_file(get_file());
  return cpp_parse(*this, log.get_message_handler());
}
