/*******************************************************************\
 
Module: A special command line object for the ld-like options
 
Author: Daniel Kroening
 
Date: Feb 2013
 
\*******************************************************************/

#ifndef GOTO_CC_LD_CMDLINE_H
#define GOTO_CC_LD_CMDLINE_H

#include "goto_cc_cmdline.h"

class ld_cmdlinet:public goto_cc_cmdlinet
{
public:
  // overload
  virtual bool parse(int, const char**);

  ld_cmdlinet()
  {
  }
};

#endif /* GOTO_CC_LD_CMDLINE_H */
