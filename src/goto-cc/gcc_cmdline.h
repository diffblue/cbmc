/*******************************************************************\
 
Module: A special command line object for the gcc-like options
 
Author: CM Wintersteiger
 
Date: June 2006
 
\*******************************************************************/

#ifndef GOTO_CC_GCC_CMDLINE_H
#define GOTO_CC_GCC_CMDLINE_H

#include "goto_cc_cmdline.h"

class gcc_cmdlinet:public goto_cc_cmdlinet
{
public:
  // overload
  virtual bool parse(int, const char**);

  gcc_cmdlinet()
  {
    mode=GCC;
  }

  // For calling the preprocessor.
  // This lets you distinguish input file name arguments
  // from others, but is otherwise identical to the
  // original command line.
  
  struct argt
  {
  public:
    argt():is_infile_name(false) { }
    explicit argt(const std::string &_arg):is_infile_name(false), arg(_arg) { }
    bool is_infile_name;
    std::string arg;
  };
  
  typedef std::list<argt> parsed_argvt;
  parsed_argvt parsed_argv;

protected:  
  void add_arg(const std::string &arg) { parsed_argv.push_back(argt(arg)); }
};

#endif /* GOTO_CC_GCC_CMDLINE_H */
