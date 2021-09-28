/*******************************************************************\

Module: Mini C Parser

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Mini C Parser

#ifndef CPROVER_CRANGLER_MINI_C_PARSER_H
#define CPROVER_CRANGLER_MINI_C_PARSER_H

#include "cscanner.h"

#include <iosfwd>
#include <vector>

#include <util/optional.h>

struct c_declarationt
{
  // could be C++20 std::span to avoid copying
  using tokenst = std::vector<ctokent>;

  tokenst pre_declarator;
  tokenst declarator;
  tokenst post_declarator;
  tokenst initializer;

  void print(std::ostream &) const;
  bool is_function() const;
  bool has_body() const;
  optionalt<ctokent> declared_identifier() const;
};

using c_translation_unitt = std::vector<c_declarationt>;

c_translation_unitt parse_c(std::istream &);

std::ostream &operator<<(std::ostream &, const c_declarationt &);

#endif // CPROVER_CRANGLER_MINI_C_PARSER_H
