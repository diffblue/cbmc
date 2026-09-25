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
  /// the `\#pragma pack(n)' in effect where this token was read (0: none);
  /// the scanner maintains the pack stack, the C++ parser reads it per
  /// declaration through the token it starts with
  int pragma_pack = 0;

  void clear()
  {
    kind=0;
    data.clear();
    text.clear();
    line_no=0;
    filename.clear();
    pragma_pack = 0;
  }

  void swap(cpp_tokent &token)
  {
    std::swap(kind, token.kind);
    std::swap(pragma_pack, token.pragma_pack);
    data.swap(token.data);
    text.swap(token.text);
    std::swap(line_no, token.line_no);
    filename.swap(token.filename);
  }
};

#endif // CPROVER_CPP_CPP_TOKEN_H
