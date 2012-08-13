/*******************************************************************\

Module: Command line interpretation for goto-cc.

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

#if 0
#ifndef GOTO_CC_CMDLINE_OPTIONS_H
#define GOTO_CC_CMDLINE_OPTIONS_H

#include "goto_cc_mode.h"
#include "goto_cc_cmdline.h"

class cmdline_optionst:public goto_cc_modet
{
public:
  goto_cc_cmdlinet &cmdline;

  // overloads
  virtual bool doit();
  virtual void help_mode();

  cmdline_optionst(goto_cc_cmdlinet &_cmdline);
  
private:
  void register_languages();
};

#endif /* GOTO_CC_CMDLINE_OPTIONS_H */
#endif
