/*******************************************************************\

Module: C++ Parser

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_PARSER_H
#define CPROVER_CPP_PARSER_H

#include <assert.h>

#include <hash_cont.h>
#include <string_hash.h>
#include <parser.h>
#include <expr.h>

#include "cpp_parse_tree.h"
#include "cpp_token_buffer.h"

class cpp_parsert:public parsert
{
public:
  cpp_parse_treet parse_tree;

  virtual bool parse();

  virtual void clear()
  {
    parsert::clear();
    parse_tree.clear();
    token_buffer.clear();
  }

public:
  // internal state
  
  enum { LANGUAGE, EXPRESSION } grammar;

  enum { ANSI, GCC, MSC, ICC, CW, ARM } mode;
  // ANSI is strict ANSI-C
  // GCC is, well, gcc
  // MSC is Microsoft Visual Studio
  // ICC is Intel's C compiler
  // CW is CodeWarrior (with GCC extensions enabled)
  // ARM is ARM's RealView

  cpp_token_buffert token_buffer;
  
  cpp_tokent &current_token()
  {
    return token_buffer.current_token();
  }
   
  void set_location()
  {
    token_buffer.current_token().line_no=line_no-1;
    token_buffer.current_token().filename=filename;
  }
  
  cpp_parsert():mode(ANSI)
  {
  }
  
  // scanner
  unsigned parenthesis_counter;
};

extern cpp_parsert cpp_parser;
int yycpperror(const std::string &error);
void cpp_scanner_init();

#endif
