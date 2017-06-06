/*******************************************************************\

Module: Base class for command line interpretation

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

/// \file
/// Base class for command line interpretation

#ifndef CPROVER_GOTO_CC_CW_MODE_H
#define CPROVER_GOTO_CC_CW_MODE_H

#include <util/cout_message.h>

#include "goto_cc_mode.h"
#include "gcc_cmdline.h"

class cw_modet:public goto_cc_modet
{
public:
  virtual int doit();
  virtual void help_mode();

  cw_modet(gcc_cmdlinet &_gcc_cmdline, const std::string &_base_name):
    goto_cc_modet(_gcc_cmdline, _base_name, message_handler),
    cmdline(_gcc_cmdline)
  {
  }

protected:
  gcc_cmdlinet &cmdline;
  console_message_handlert message_handler;
};

#endif // CPROVER_GOTO_CC_CW_MODE_H
