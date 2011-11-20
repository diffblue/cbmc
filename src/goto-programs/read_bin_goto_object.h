/*******************************************************************\
 
Module: Read goto object files.
 
Author: CM Wintersteiger
 
Date: May 2007
 
\*******************************************************************/

#ifndef READ_BIN_GOTO_OBJECT_H_
#define READ_BIN_GOTO_OBJECT_H_

#include <istream>
#include <string>

class contextt;
class goto_functionst;
class message_handlert;

bool read_bin_goto_object(
  std::istream &in,
  const std::string &filename,
  contextt &context,
  goto_functionst &functions,
  message_handlert &message_handler);

#endif /*READ_BIN_GOTO_OBJECT_H_*/
