/*******************************************************************\

Module: Command line interpretation for goto-cc

Author: Daniel Kroening

Date:   April 2010

\*******************************************************************/

#ifndef GOTO_CC_CMDLINE_H
#define GOTO_CC_CMDLINE_H

#include <util/cmdline.h>

class goto_cc_cmdlinet:public cmdlinet
{
public:
  using cmdlinet::parse;
  virtual bool parse(int argc, const char **argv)=0;
  
  static bool in_list(const char *option, const char **list);

  static bool prefix_in_list(
    const char *option,
    const char **list,
    std::string &prefix);

  // never fails, will add if not found
  std::size_t get_optnr(const std::string &option);

  void set(const std::string &opt, const std::string &value)
  {
    std::size_t nr=get_optnr(opt);
    options[nr].isset=true;
    options[nr].values.push_back(value);
  }
  
  void set(const std::string &opt)
  {
    options[get_optnr(opt)].isset=true;
  }

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
  
  bool have_infile_arg() const
  {
    for(parsed_argvt::const_iterator
        it=parsed_argv.begin(); it!=parsed_argv.end(); it++)
      if(it->is_infile_name) return true;
    return false;
  }

protected:  
  void add_arg(const std::string &arg)
  {
    parsed_argv.push_back(argt(arg));
  }

  void add_infile_arg(const std::string &arg)
  {
    parsed_argv.push_back(argt(arg));
    parsed_argv.back().is_infile_name=true;
  }
};

#endif /* GOTO_CC_CMDLINE_H */
