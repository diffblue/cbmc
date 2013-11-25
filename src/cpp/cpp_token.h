/*******************************************************************\

Module: C++ Parser: Token

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_TOKEN_H
#define CPROVER_CPP_TOKEN_H

#include <algorithm>

#include <util/expr.h>

class cpp_tokent
{
public:
  int kind;
  exprt data;
  std::string text;
  unsigned line_no;
  irep_idt filename;
  unsigned pos;
  
  void clear()
  {
    kind=0;
    data.clear();
    text="";
    line_no=0;
    filename="";
    pos=0;
  }
  
  void swap(cpp_tokent &token)
  {
    std::swap(kind, token.kind);
    data.swap(token.data);
    text.swap(token.text);
    std::swap(line_no, token.line_no);
    filename.swap(token.filename);
    std::swap(pos, token.pos);    
  }
};

#endif
