/*******************************************************************\

Module: Visual Studio CL Mode

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

#ifndef CPROVER_GOTO_CC_MS_CL_MODE_H
#define CPROVER_GOTO_CC_MS_CL_MODE_H

#include <util/cout_message.h>

#include "goto_cc_mode.h"
#include "ms_cl_cmdline.h"

class ms_cl_modet:public goto_cc_modet
{
public:
  virtual int doit();
  virtual void help_mode();

  explicit ms_cl_modet(ms_cl_cmdlinet &_ms_cl_cmdline):
    goto_cc_modet(_ms_cl_cmdline, message_handler),
    cmdline(_ms_cl_cmdline)
  {
  }

protected:
  ms_cl_cmdlinet &cmdline;
  console_message_handlert message_handler;
};

#endif // CPROVER_GOTO_CC_MS_CL_MODE_H
