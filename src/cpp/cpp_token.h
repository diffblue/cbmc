/*******************************************************************\

Module: C++ Parser: Token

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Parser: Token

#ifndef CPROVER_CPP_CPP_TOKEN_H
#define CPROVER_CPP_CPP_TOKEN_H

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

  void clear()
  {
    kind=0;
    data.clear();
    text.clear();
    line_no=0;
    filename.clear();
  }

  void swap(cpp_tokent &token)
  {
    std::swap(kind, token.kind);
    data.swap(token.data);
    text.swap(token.text);
    std::swap(line_no, token.line_no);
    filename.swap(token.filename);
  }
};

#endif // CPROVER_CPP_CPP_TOKEN_H
