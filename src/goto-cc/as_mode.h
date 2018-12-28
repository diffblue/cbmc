/*******************************************************************\

Module: Assembler Mode

Author: Michael Tautschnig

Date: July 2016

\*******************************************************************/

/// \file
/// Assembler Mode

#ifndef CPROVER_GOTO_CC_AS_MODE_H
#define CPROVER_GOTO_CC_AS_MODE_H

#include "gcc_message_handler.h"
#include "goto_cc_mode.h"

class as_modet:public goto_cc_modet
{
public:
  virtual int doit();
  virtual void help_mode();

  as_modet(
    goto_cc_cmdlinet &_cmdline,
    const std::string &_base_name,
    bool _produce_hybrid_binary);

protected:
  gcc_message_handlert message_handler;
  const bool produce_hybrid_binary;
  const std::string native_tool_name;

  int run_as(); // call as with original command line

  int as_hybrid_binary();
};

#endif // CPROVER_GOTO_CC_AS_MODE_H
