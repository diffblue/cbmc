/*******************************************************************\

Module: Base class for command line interpretation

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

#ifndef CPROVER_GOTO_CC_GCC_MODE_H
#define CPROVER_GOTO_CC_GCC_MODE_H

#include <util/cout_message.h>

#include "goto_cc_mode.h"
#include "gcc_cmdline.h"

class gcc_modet:public goto_cc_modet
{
public:
  int doit() final;
  void help_mode() final;

  explicit gcc_modet(goto_cc_cmdlinet &_cmdline):
    goto_cc_modet(_cmdline, gcc_message_handler),
    produce_hybrid_binary(false),
    act_as_ld(false)
  {
  }

  bool produce_hybrid_binary;

protected:
  gcc_message_handlert gcc_message_handler;
  bool act_as_ld;
  std::string native_compiler_name;

  int preprocess(
    const std::string &language,
    const std::string &src,
    const std::string &dest);

  int run_gcc(); // call gcc with original command line

  int gcc_hybrid_binary();

  static bool needs_preprocessing(const std::string &);

  inline const char *compiler_name()
  {
    if(native_compiler_name.empty())
    {
      std::string::size_type pos=base_name.find("goto-gcc");

      if(pos==std::string::npos ||
         base_name=="goto-gcc" ||
         base_name=="goto-ld")
      {
        #ifdef __FreeBSD__
        native_compiler_name="clang";
        #else
        native_compiler_name="gcc";
        #endif
      }
      else
      {
        native_compiler_name=base_name;
        native_compiler_name.replace(pos, 8, "gcc");
      }
    }

    return native_compiler_name.c_str();
  }

  inline const char *linker_name()
  {
    if(native_compiler_name.empty())
    {
      std::string::size_type pos=base_name.find("goto-ld");

      if(pos==std::string::npos ||
         base_name=="goto-gcc" ||
         base_name=="goto-ld")
      {
        native_compiler_name="ld";
      }
      else
      {
        native_compiler_name=base_name;
        native_compiler_name.replace(pos, 7, "ld");
      }
    }

    return native_compiler_name.c_str();
  }
};

#endif // CPROVER_GOTO_CC_GCC_MODE_H
