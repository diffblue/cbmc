/*******************************************************************\

Module: Base class for command line interpretation for CL

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

/// \file
/// Base class for command line interpretation for CL

#ifndef CPROVER_GOTO_CC_ARMCC_MODE_H
#define CPROVER_GOTO_CC_ARMCC_MODE_H

#include "armcc_cmdline.h"
#include "gcc_message_handler.h"
#include "goto_cc_mode.h"

class armcc_modet:public goto_cc_modet
{
public:
  int doit() final;
  void help_mode() final;

  armcc_modet(
    armcc_cmdlinet &_armcc_cmdline,
    const std::string &_base_name):
    goto_cc_modet(_armcc_cmdline, _base_name, message_handler),
    cmdline(_armcc_cmdline)
  {
  }

protected:
  armcc_cmdlinet &cmdline;
  gcc_message_handlert message_handler;
};

#endif // CPROVER_GOTO_CC_ARMCC_MODE_H
