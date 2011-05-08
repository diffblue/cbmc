/*******************************************************************\
 
Module: Read goto object files.
 
Author: CM Wintersteiger
 
Date: June 2006
 
\*******************************************************************/

#ifndef READ_GOTO_OBJECT_H_
#define READ_GOTO_OBJECT_H_

#include <message.h>
#include <context.h>
#include <goto-programs/goto_functions.h>

bool read_goto_object(
  std::istream &in,
  const std::string &filename,
  contextt &context,
  goto_functionst &functions,
  message_handlert &msg_hndlr);

#endif /*READ_GOTO_OBJECT_H_*/
