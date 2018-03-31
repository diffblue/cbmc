/*******************************************************************\
 
Module: A special command line object for as86 (of Bruce's C Compiler)
 
Author: Michael Tautschnig
 
Date: July 2016
 
\*******************************************************************/

/// \file
///  A special command line object for as86 (of Bruce's C Compiler) Author:
///   Michael Tautschnig Date: July 2016

#ifndef CPROVER_GOTO_CC_AS86_CMDLINE_H
#define CPROVER_GOTO_CC_AS86_CMDLINE_H

#include "goto_cc_cmdline.h"

class as86_cmdlinet:public goto_cc_cmdlinet
{
public:
  // overload
  virtual bool parse(int, const char**);

  as86_cmdlinet()
  {
  }
};

#endif // CPROVER_GOTO_CC_AS86_CMDLINE_H
