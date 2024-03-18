/*******************************************************************\

Module: C++ Parser: Token Buffer

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Parser: Token Buffer

#ifndef CPROVER_CPP_CPP_TOKEN_BUFFER_H
#define CPROVER_CPP_CPP_TOKEN_BUFFER_H

#include <util/config.h>
#include <util/invariant.h>

#include <ansi-c/ansi_c_parser.h>

#include "cpp_token.h"

#include <list>

class cpp_token_buffert
{
public:
  explicit cpp_token_buffert(message_handlert &message_handler)
    : ansi_c_parser(message_handler), current_pos(0)
  {
    // We use the ANSI-C scanner
    ansi_c_parser.cpp98 = true;
    ansi_c_parser.cpp11 =
      config.cpp.cpp_standard == configt::cppt::cpp_standardt::CPP11 ||
      config.cpp.cpp_standard == configt::cppt::cpp_standardt::CPP14 ||
      config.cpp.cpp_standard == configt::cppt::cpp_standardt::CPP17;
    ansi_c_parser.ts_18661_3_Floatn_types = false;
    ansi_c_parser.mode = config.ansi_c.mode;
    ansi_c_scanner_init(ansi_c_parser);
  }

  typedef unsigned int post;

  int LookAhead(unsigned offset);
  int get_token(cpp_tokent &token);
  int get_token();
  int LookAhead(unsigned offset, cpp_tokent &token);

  post Save();
  void Restore(post pos);
  void Replace(const cpp_tokent &token);
  void Insert(const cpp_tokent &token);

  void clear()
  {
    tokens.clear();
    token_vector.clear();
    current_pos=0;
  }

  // the token that is currently being read from the file
  cpp_tokent &current_token()
  {
    PRECONDITION(!tokens.empty());
    return tokens.back();
  }

  ansi_c_parsert ansi_c_parser;

protected:
  typedef std::list<cpp_tokent> tokenst;
  tokenst tokens;

  std::vector<tokenst::iterator> token_vector;

  post current_pos;

  void *ansi_c_scanner_state;

  // get another token from lexer
  void read_token();
};

#endif // CPROVER_CPP_CPP_TOKEN_BUFFER_H
