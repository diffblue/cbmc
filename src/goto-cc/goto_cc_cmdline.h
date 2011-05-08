/*******************************************************************\

Module: Command line interpretation for goto-cc

Author: Daniel Kroening

Date:   April 2010

\*******************************************************************/

#ifndef GOTO_CC_CMDLINE_H
#define GOTO_CC_CMDLINE_H

#include <cmdline.h>

class goto_cc_cmdlinet:public cmdlinet
{
public:
  typedef enum { VISUAL_STUDIO, GCC, CODEWARRIOR, ARM } modet;
  modet mode;

  virtual bool parse(int argc, const char **argv)=0;
  
  static bool in_list(const char *option, const char **list);

  static bool prefix_in_list(
    const char *option,
    const char **list,
    std::string &prefix);

  int get_optnr(const std::string &option);
};

#endif /*CMDLINE_H_*/
