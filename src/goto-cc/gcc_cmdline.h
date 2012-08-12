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
  virtual bool parse(int, const char**);

  gcc_cmdlinet()
  {
    mode=GCC;
  }

protected:  
  int option_nr(const std::string &opt);
  
  void set(const std::string &opt, const std::string &value)
  {
    int nr=option_nr(opt);
    options[nr].isset=true;
    options[nr].values.push_back(value);
  }
  
  void set(const std::string &opt)
  {
    options[option_nr(opt)].isset=true;
  }

  // for calling the preprocessor
  struct argt
  {
  public:
    argt():is_infile_name(false) { }
    explicit argt(const std::string &_arg):is_infile_name(false), arg(_arg) { }
    bool is_infile_name;
    std::string arg;
  };
  
  std::list<argt> new_argv;
  
  void add_arg(const std::string &arg) { new_argv.push_back(argt(arg)); }
};

#endif /* GOTO_CC_GCC_CMDLINE_H */
