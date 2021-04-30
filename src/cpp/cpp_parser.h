/*******************************************************************\

Module: C++ Parser

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Parser

#ifndef CPROVER_CPP_CPP_PARSER_H
#define CPROVER_CPP_CPP_PARSER_H

#include <util/parser.h>

#include <ansi-c/ansi_c_parser.h>

#include "cpp_parse_tree.h"
#include "cpp_token_buffer.h"

class cpp_parsert:public parsert
{
public:
  cpp_parse_treet parse_tree;

  virtual bool parse() override;

  virtual void clear() override
  {
    parsert::clear();
    parse_tree.clear();
    token_buffer.clear();
    asm_block_following=false;
  }

  cpp_parsert():
    mode(configt::ansi_ct::flavourt::ANSI),
    recognize_wchar_t(true),
    asm_block_following(false)
  {
  }

public:
  // internal state
  ansi_c_parsert::modet mode;

  // We can furthermore twiddle the recognition of various
  // keywords. This is honored in particular modes.
  bool recognize_wchar_t;

  cpp_token_buffert token_buffer;

  cpp_tokent &current_token()
  {
    return token_buffer.current_token();
  }

  void add_location()
  {
    token_buffer.current_token().line_no=get_line_no()-1;
    token_buffer.current_token().filename=source_location.get_file();
  }

  // scanner
  unsigned parenthesis_counter;
  bool asm_block_following;
};

extern cpp_parsert cpp_parser;

#endif // CPROVER_CPP_CPP_PARSER_H
