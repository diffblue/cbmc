/*******************************************************************\

Module: C++ Parser: Token Buffer

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Parser: Token Buffer

#ifndef CPROVER_CPP_CPP_TOKEN_BUFFER_H
#define CPROVER_CPP_CPP_TOKEN_BUFFER_H

#include "cpp_token.h"

#include <list>

#include <util/invariant.h>

class cpp_token_buffert
{
public:
  cpp_token_buffert():current_pos(0)
  {
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

protected:
  typedef std::list<cpp_tokent> tokenst;
  tokenst tokens;

  std::vector<tokenst::iterator> token_vector;

  post current_pos;

  // get another token from lexer
  void read_token();
};

#endif // CPROVER_CPP_CPP_TOKEN_BUFFER_H
