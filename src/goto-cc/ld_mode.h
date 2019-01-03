/*******************************************************************\

Module: Base class for command line interpretation

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

/// \file
/// Base class for command line interpretation

#ifndef CPROVER_GOTO_CC_LD_MODE_H
#define CPROVER_GOTO_CC_LD_MODE_H

#include "compile.h"
#include "gcc_message_handler.h"
#include "goto_cc_mode.h"

#include <set>

class ld_modet : public goto_cc_modet
{
public:
  int doit() final;
  void help_mode() final;

  ld_modet(
    goto_cc_cmdlinet &_cmdline,
    const std::string &_base_name);

protected:
  gcc_message_handlert gcc_message_handler;

  std::string native_tool_name;

  const std::string goto_binary_tmp_suffix;

  /// \brief call ld with original command line
  int run_ld();

  int ld_hybrid_binary(compilet &compiler);
};

#endif // CPROVER_GOTO_CC_LD_MODE_H
