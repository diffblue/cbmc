/*******************************************************************\

Module: Base class for command line interpretation for CL

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

#ifndef GOTO_CC_MS_CL_MODE_H
#define GOTO_CC_MS_CL_MODE_H

#include "goto_cc_mode.h"
#include "ms_cl_cmdline.h"

class ms_cl_modet:public goto_cc_modet
{
public:
  virtual bool doit();
  virtual void help_mode();

  explicit ms_cl_modet(ms_cl_cmdlinet &_ms_cl_cmdline):
    goto_cc_modet(_ms_cl_cmdline),
    cmdline(_ms_cl_cmdline)
  {
  }
  
protected:
  ms_cl_cmdlinet &cmdline;
};

#endif /* GOTO_CC_MS_CL_MODE_H */
