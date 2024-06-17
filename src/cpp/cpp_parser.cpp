/*******************************************************************\

Module: C++ Parser

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Parser

#include "cpp_parser.h"

#include <util/config.h>

#include <ansi-c/gcc_version.h>

bool cpp_parse(cpp_parsert &, message_handlert &);

bool cpp_parsert::parse()
{
  if(!support_float16.has_value())
  {
    if(config.ansi_c.preprocessor == configt::ansi_ct::preprocessort::GCC)
    {
      gcc_versiont gcc_version;
      gcc_version.get("gcc");
      support_float16 = gcc_version.flavor == gcc_versiont::flavort::GCC &&
                        gcc_version.is_at_least(13u);
    }
    else
      support_float16 = false;
  }

  // We use the ANSI-C scanner
  token_buffer.ansi_c_parser.cpp98 = true;
  token_buffer.ansi_c_parser.cpp11 =
    config.cpp.cpp_standard == configt::cppt::cpp_standardt::CPP11 ||
    config.cpp.cpp_standard == configt::cppt::cpp_standardt::CPP14 ||
    config.cpp.cpp_standard == configt::cppt::cpp_standardt::CPP17;
  token_buffer.ansi_c_parser.ts_18661_3_Floatn_types =
    false; // these are still typedefs
  token_buffer.ansi_c_parser.__float128_is_keyword = false;
  token_buffer.ansi_c_parser.float16_type = *support_float16;
  token_buffer.ansi_c_parser.bf16_type = *support_float16;
  token_buffer.ansi_c_parser.fp16_type = *support_float16;
  token_buffer.ansi_c_parser.in = in;
  token_buffer.ansi_c_parser.mode = mode;
  token_buffer.ansi_c_parser.set_file(get_file());

  return cpp_parse(*this, log.get_message_handler());
}
