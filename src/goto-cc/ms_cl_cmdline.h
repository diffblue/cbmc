/*******************************************************************\
 
Module: A special command line object for the gcc-like options
 
Author: CM Wintersteiger
 
Date: June 2006
 
\*******************************************************************/

#ifndef GOTO_CC_MS_CL_CMDLINE_H
#define GOTO_CC_MS_CL_CMDLINE_H

#include "goto_cc_cmdline.h"

class ms_cl_cmdlinet:public goto_cc_cmdlinet
{
public:
  virtual bool parse(int, const char **);

  ms_cl_cmdlinet()
  {
    mode=VISUAL_STUDIO;
  }
  
  void parse_env();
  
protected:
  void process_non_cl_option(const std::string &s);
  void process_cl_option(const std::string &s);
  void process_response_file(const std::string &file);
  void process_response_file_line(const std::string &line);
  bool parse(const std::vector<std::string> &);
};

#endif /*MS_CL_CMDLINE_H_*/
