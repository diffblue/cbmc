/*******************************************************************\

Module: C Token

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// ctoken

#ifndef CPROVER_CRANGLER_CTOKEN_H
#define CPROVER_CRANGLER_CTOKEN_H

#include <iosfwd>
#include <string>

class ctokent
{
public:
  using kindt = enum {
    END_OF_FILE,
    INT_LIT,
    CHAR_LIT,
    FLOAT_LIT,
    STRING_LIT,
    C_COMMENT,
    CPP_COMMENT,
    IDENTIFIER,
    OPERATOR,
    WS,
    SEPARATOR,
    PREPROCESSOR_DIRECTIVE,
    UNKNOWN
  };

  kindt kind;

  // could be string_view, after C++17
  std::string text;

  std::size_t line_number = 0;

  ctokent() = default;

  ctokent(kindt _kind, std::string _text) : kind(_kind), text(std::move(_text))
  {
  }

  void output(std::ostream &) const;

  bool operator==(const char *other_text) const
  {
    return text == other_text;
  }

  bool operator==(char some_char) const
  {
    return text == std::string(1, some_char);
  }

  bool operator!=(char some_char) const
  {
    return text != std::string(1, some_char);
  }
};

static inline bool is_identifier(const ctokent &t)
{
  return t.kind == ctokent::IDENTIFIER;
}

static inline bool is_separator(const ctokent &t)
{
  return t.kind == ctokent::SEPARATOR;
}

static inline bool is_operator(const ctokent &t)
{
  return t.kind == ctokent::OPERATOR;
}

static inline bool is_ws(const ctokent &t)
{
  return t.kind == ctokent::WS;
}

static inline bool is_eof(const ctokent &t)
{
  return t.kind == ctokent::END_OF_FILE;
}

static inline bool is_comment(const ctokent &t)
{
  return t.kind == ctokent::C_COMMENT || t.kind == ctokent::CPP_COMMENT;
}

static inline bool is_preprocessor_directive(const ctokent &t)
{
  return t.kind == ctokent::PREPROCESSOR_DIRECTIVE;
}

std::ostream &operator<<(std::ostream &, const ctokent &);

#endif // CPROVER_CRANGLER_CTOKEN_H
