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

  //typedef std::list<argt> parsed_argvt;
  //parsed_argvt parsed_argv;

//protected:  
  //void add_arg(const std::string &arg) { parsed_argv.push_back(argt(arg)); }
};

#endif /* GOTO_CC_LD_CMDLINE_H */
