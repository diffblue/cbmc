/*******************************************************************\

Module: C Scanner

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// cscanner

#ifndef CPROVER_CRANGLER_CSCANNER_H
#define CPROVER_CRANGLER_CSCANNER_H

#include <iosfwd>
#include <vector>

#include "ctoken.h"

class cscannert
{
public:
  explicit cscannert(std::istream &);
  ~cscannert();

  ctokent operator()();

  std::istream &in;
  std::size_t line_number = 1;

  bool return_WS_and_comments = false;

  void set_token(std::string text, ctokent::kindt kind)
  {
    token.line_number = line_number;
    token.text = std::move(text);
    token.kind = kind;
  }

  std::vector<ctokent> get_tokens();

protected:
  ctokent token;
};

extern cscannert *cscanner_ptr;

#endif // CPROVER_CRANGLER_CSCANNER_H
