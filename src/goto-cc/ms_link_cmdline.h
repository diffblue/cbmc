/*******************************************************************\

Module: A special command line object for LINK options

Author: Daniel Kroening

Date: July 2018

\*******************************************************************/

/// \file
/// A special command line object for LINK options

#ifndef CPROVER_GOTO_CC_MS_LINK_CMDLINE_H
#define CPROVER_GOTO_CC_MS_LINK_CMDLINE_H

#include "goto_cc_cmdline.h"

class ms_link_cmdlinet : public goto_cc_cmdlinet
{
public:
  virtual bool parse(int, const char **);

  ms_link_cmdlinet()
  {
  }

protected:
  void process_non_link_option(const std::string &s);
  void process_link_option(const std::string &s);
  void process_response_file(const std::string &file);
  void process_response_file_line(const std::string &line);
  bool parse(const std::vector<std::string> &);
};

#endif // CPROVER_GOTO_CC_MS_LINK_CMDLINE_H
