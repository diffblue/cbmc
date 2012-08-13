/*******************************************************************\

Module: Base class for command line interpretation

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

#ifndef GOTO_CC_GCC_MODE_H
#define GOTO_CC_GCC_MODE_H

#include "goto_cc_mode.h"
#include "gcc_cmdline.h"

class gcc_modet:public goto_cc_modet
{
public:
  virtual bool doit();
  virtual void help_mode();

  explicit gcc_modet(gcc_cmdlinet &_gcc_cmdline):
    goto_cc_modet(_gcc_cmdline),
    cmdline(_gcc_cmdline)
  {
  }
  
protected:
  gcc_cmdlinet &cmdline;
  
  int preprocess(const std::string &src, const std::string &dest);
};

#endif /* GOTO_CC_GCC_MODE_H */
