/*******************************************************************\

Module: C++ Parser

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_PARSER_H
#define CPROVER_CPP_PARSER_H

#include <cassert>

#include <util/hash_cont.h>
#include <util/string_hash.h>
#include <util/parser.h>
#include <util/expr.h>

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
    asm_block_following=false;
  }
  
  cpp_parsert():
    mode(ANSI),
    recognize_wchar_t(true),
    asm_block_following(false)    
  {
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
  
  // We can furthermore twiddle the recognition of various
  // keywords. This is honored in particular modes.
  bool recognize_wchar_t;

  cpp_token_buffert token_buffer;
  
  cpp_tokent &current_token()
  {
    return token_buffer.current_token();
  }
   
  void set_location()
  {
    token_buffer.current_token().line_no=get_line_no()-1;
    token_buffer.current_token().filename=location.get_file();
  }
  
  // scanner
  unsigned parenthesis_counter;
  bool asm_block_following;
  std::string string_literal;

  bool tag_following; // not used
};

extern cpp_parsert cpp_parser;
void cpp_scanner_init();

#endif
