/*******************************************************************\

Module: Base class for command line interpretation

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

#ifndef GOTO_CC_CW_MODE_H
#define GOTO_CC_CW_MODE_H

#include "goto_cc_mode.h"
#include "cw_cmdline.h"

class cw_modet:public goto_cc_modet
{
public:
  virtual bool doit();
  virtual void help_mode();

  explicit cw_modet(cw_cmdlinet &_cw_cmdline):
    goto_cc_modet(_cw_cmdline),
    cmdline(_cw_cmdline)
  {
  }
  
protected:
  cw_cmdlinet &cmdline;
};

#endif /* GOTO_CC_CW_MODE_H */
