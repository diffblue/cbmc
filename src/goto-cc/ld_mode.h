/*******************************************************************\

Module: Base class for command line interpretation

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

#ifndef CPROVER_GOTO_CC_LD_MODE_H
#define CPROVER_GOTO_CC_LD_MODE_H

#include <util/cout_message.h>

#include "goto_cc_mode.h"
#include "ld_cmdline.h"

class ld_modet:public goto_cc_modet
{
public:
  int doit() final;
  void help_mode() final;

  explicit ld_modet(ld_cmdlinet &_ld_cmdline):
    goto_cc_modet(_ld_cmdline, message_handler),
    produce_hybrid_binary(false),
    cmdline(_ld_cmdline)
  {
  }

  bool produce_hybrid_binary;

protected:
  ld_cmdlinet &cmdline;
  gcc_message_handlert message_handler;

  //int gcc_hybrid_binary(const cmdlinet::argst &input_files);
  //static bool is_supported_source_file(const std::string &);
};

#endif // CPROVER_GOTO_CC_LD_MODE_H
