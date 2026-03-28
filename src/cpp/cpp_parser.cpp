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
    else if(
      config.ansi_c.preprocessor == configt::ansi_ct::preprocessort::CLANG)
    {
      // Apple Clang supports _Float16 natively. On macOS, system headers
      // use _Float16 without typedefs. On Linux with clang, glibc headers
      // typedef _Float32 etc., which conflicts with keyword mode.
#ifdef __APPLE__
      support_float16 = true;
#else
      support_float16 = false;
#endif
    }
    else
      support_float16 = false;
  }

  // We use the ANSI-C scanner
  token_buffer.ansi_c_parser.cpp98 = true;
  token_buffer.ansi_c_parser.cpp11 =
    config.cpp.cpp_standard >= configt::cppt::cpp_standardt::CPP11;
  token_buffer.ansi_c_parser.cpp20 =
    config.cpp.cpp_standard >= configt::cppt::cpp_standardt::CPP20;
  // _Float32/64/32x/64x are TS 18661-3 types. GCC 13+ supports them
  // as built-in types in C++ mode; older GCC and clang do not.
  token_buffer.ansi_c_parser.ts_18661_3_Floatn_types = *support_float16;
  token_buffer.ansi_c_parser.__float128_is_keyword = false;
  token_buffer.ansi_c_parser.float16_type = *support_float16;
  token_buffer.ansi_c_parser.bf16_type = *support_float16;
  token_buffer.ansi_c_parser.fp16_type = *support_float16;
  // __remove_cv, __remove_reference, __remove_cvref are GCC 13+ builtins.
  // Older libstdc++ uses these as regular identifiers (template aliases).
  token_buffer.ansi_c_parser.gcc13_type_traits =
    *support_float16 ||
    config.ansi_c.preprocessor == configt::ansi_ct::preprocessort::CLANG;
  // GCC 14+ uses __is_array, __is_function, __is_reference, etc. as builtins
  // in <type_traits>. Older GCC uses template specialization instead.
  {
    bool is_gcc14 = false;
    if(config.ansi_c.preprocessor == configt::ansi_ct::preprocessort::GCC)
    {
      gcc_versiont gcc_version;
      gcc_version.get("gcc");
      is_gcc14 = gcc_version.flavor == gcc_versiont::flavort::GCC &&
                 gcc_version.is_at_least(14u);
    }
    token_buffer.ansi_c_parser.gcc14_builtins =
      is_gcc14 ||
      config.ansi_c.preprocessor == configt::ansi_ct::preprocessort::CLANG;
  }
  token_buffer.ansi_c_parser.in = in;
  token_buffer.ansi_c_parser.mode = mode;
  token_buffer.ansi_c_parser.set_file(get_file());

  return cpp_parse(*this, log.get_message_handler());
}
