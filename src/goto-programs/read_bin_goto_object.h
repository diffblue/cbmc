/*******************************************************************\
 
Module: Read goto object files.
 
Author: CM Wintersteiger
 
Date: May 2007
 
\*******************************************************************/

#ifndef CPROVER_READ_BIN_GOTO_OBJECT_H
#define CPROVER_READ_BIN_GOTO_OBJECT_H

#include <istream>
#include <string>

class symbol_tablet;
class goto_functionst;
class message_handlert;

bool read_bin_goto_object(
  std::istream &in,
  const std::string &filename,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  message_handlert &message_handler);

#endif /*READ_BIN_GOTO_OBJECT_H_*/
