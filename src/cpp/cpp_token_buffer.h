/*******************************************************************\

Module: C++ Parser: Token Buffer

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_TOKEN_BUFFER_H
#define CPROVER_CPP_TOKEN_BUFFER_H

#include "cpp_token.h"

class cpp_token_buffert
{
public:
  cpp_token_buffert():current_pos(0)
  {
  }
 
  typedef unsigned int post;
 
  int LookAhead(unsigned offset);
  int GetToken(cpp_tokent &token);
  int GetToken();
  int LookAhead(unsigned offset, cpp_tokent &token);

  post Save();
  void Restore(post pos);
  
  void clear()
  {
    tokens.clear();
    token_vector.clear();
    current_pos=0;
  }

  // the token that is currently being read from the file
  cpp_tokent &current_token()
  {
    assert(!tokens.empty());
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

#endif
