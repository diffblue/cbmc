/*******************************************************************\

Module: Base class for command line interpretation for CL

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

#ifndef GOTO_CC_ARMCC_MODE_H
#define GOTO_CC_ARMCC_MODE_H

#include "goto_cc_mode.h"
#include "armcc_cmdline.h"

class armcc_modet:public goto_cc_modet
{
public:
  virtual bool doit();
  virtual void help_mode();

  explicit armcc_modet(armcc_cmdlinet &_armcc_cmdline):
    goto_cc_modet(_armcc_cmdline),
    cmdline(_armcc_cmdline)
  {
  }
  
protected:
  armcc_cmdlinet &cmdline;
};

#endif /* GOTO_CC_ARMCC_MODE_H */
