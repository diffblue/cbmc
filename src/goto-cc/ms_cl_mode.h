/*******************************************************************\

Module: Visual Studio CL Mode

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

#ifndef CPROVER_GOTO_CC_MS_CL_MODE_H
#define CPROVER_GOTO_CC_MS_CL_MODE_H

#include "goto_cc_mode.h"
#include "ms_cl_cmdline.h"

class ms_cl_modet:public goto_cc_modet
{
public:
  virtual int doit();
  virtual void help_mode();

  ms_cl_modet(
    ms_cl_cmdlinet &_ms_cl_cmdline,
    const std::string &_base_name):
    goto_cc_modet(_ms_cl_cmdline, _base_name),
    cmdline(_ms_cl_cmdline)
  {
  }

protected:
  ms_cl_cmdlinet &cmdline;
};

#endif // CPROVER_GOTO_CC_MS_CL_MODE_H
