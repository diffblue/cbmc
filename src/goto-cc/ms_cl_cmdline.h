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
  void process_non_cl_option(const std::wstring &s);
  void process_cl_option(const std::wstring &s);
  void process_response_file(const std::string &file);
  void process_response_file_line(const std::wstring &line);
  bool parse(const std::vector<std::wstring> &);
  
  static std::string w2s(const std::wstring &ws)
  {
    std::string simple_string;
    simple_string.assign(ws.begin(), ws.end());
    return simple_string;
  }

  static std::wstring s2w(const std::string &s)
  {
    std::wstring wide_string;
    wide_string.assign(s.begin(), s.end());
    return wide_string;
  }
};

#endif /*MS_CL_CMDLINE_H_*/
