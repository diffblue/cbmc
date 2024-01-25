/*******************************************************************\

Module: C++ Parser

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Parser

#include "cpp_parser.h"

#include <util/config.h>

#include <ansi-c/gcc_version.h>

cpp_parsert cpp_parser;

bool cpp_parse();

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
  ansi_c_parser.cpp98=true;
  ansi_c_parser.cpp11 =
    config.cpp.cpp_standard == configt::cppt::cpp_standardt::CPP11 ||
    config.cpp.cpp_standard == configt::cppt::cpp_standardt::CPP14 ||
    config.cpp.cpp_standard == configt::cppt::cpp_standardt::CPP17;
  ansi_c_parser.ts_18661_3_Floatn_types = false; // these are still typedefs
  ansi_c_parser.float16_type = *support_float16;
  ansi_c_parser.bf16_type = *support_float16;
  ansi_c_parser.in=in;
  ansi_c_parser.mode=mode;
  ansi_c_parser.set_file(get_file());
  ansi_c_parser.log.set_message_handler(log.get_message_handler());

  return cpp_parse();
}
