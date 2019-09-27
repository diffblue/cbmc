/*******************************************************************\

Module: Command line interpretation for goto-cc

Author: Daniel Kroening

Date:   April 2010

\*******************************************************************/

/// \file
/// Command line interpretation for goto-cc

#ifndef CPROVER_GOTO_CC_GOTO_CC_CMDLINE_H
#define CPROVER_GOTO_CC_GOTO_CC_CMDLINE_H

#include <util/cmdline.h>

class goto_cc_cmdlinet:public cmdlinet
{
public:
  ~goto_cc_cmdlinet();

  using cmdlinet::parse;
  virtual bool parse(int argc, const char **argv)=0;

  static bool in_list(const char *option, const char **list);

  static bool prefix_in_list(
    const char *option,
    const char **list,
    std::string &prefix);

  // never fails, will add if not found
  std::size_t get_optnr(const std::string &option);

  void set(const std::string &opt, const std::string &value) override
  {
    std::size_t nr=get_optnr(opt);
    options[nr].isset=true;
    options[nr].values.push_back(value);
  }

  void set(const std::string &opt, bool value = true) override
  {
    options[get_optnr(opt)].isset = value;
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
      if(it->is_infile_name)
        return true;
    return false;
  }

  std::string stdin_file;

protected:
  void add_arg(const std::string &arg)
  {
    parsed_argv.push_back(argt(arg));
  }

  void add_infile_arg(const std::string &arg);
};

#endif // CPROVER_GOTO_CC_GOTO_CC_CMDLINE_H
