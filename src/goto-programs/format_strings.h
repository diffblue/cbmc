/*******************************************************************\

Module: Format String Parser

Author: CM Wintersteiger

\*******************************************************************/

/// \file
/// Format String Parser

#ifndef CPROVER_GOTO_PROGRAMS_FORMAT_STRINGS_H
#define CPROVER_GOTO_PROGRAMS_FORMAT_STRINGS_H

#include <string>
#include <list>

#include <util/expr.h>
#include <util/mp_arith.h>

class format_tokent
{
public:
  enum class token_typet
  {
    UNKNOWN,
    TEXT,
    INT, // d, i, o, u, x
    FLOAT, // a, e, f, g
    CHAR, // c
    STRING, // s
    POINTER // p
  };

  enum class flag_typet
  {
    ALTERNATE,
    ZERO_PAD,
    LEFT_ADJUST,
    SIGNED_SPACE,
    SIGN,
    ASTERISK
  };

  enum class length_modifierst
  {
    LEN_undef,
    LEN_h,
    LEN_hh,
    LEN_l,
    LEN_ll,
    LEN_L,
    LEN_j,
    LEN_t
  };

  enum class representationt
  {
    SIGNED_undef,
    SIGNED_DEC,
    UNSIGNED_DEC,
    UNSIGNED_OCT,
    UNSIGNED_HEX
  };

  explicit format_tokent(token_typet _type)
    : type(_type),
      length_modifier(length_modifierst::LEN_undef),
      representation(representationt::SIGNED_undef)
    { }
  format_tokent():
    type(token_typet::UNKNOWN),
    length_modifier(length_modifierst::LEN_undef),
    representation(representationt::SIGNED_undef)
    { }


  token_typet type;
  std::list<flag_typet> flags;
  mp_integer field_width;
  mp_integer precision;
  length_modifierst length_modifier;
  representationt representation;
  irep_idt value; // for text and pattern matching
};

typedef std::list<format_tokent> format_token_listt;

format_token_listt parse_format_string(const std::string &);

optionalt<typet> get_type(const format_tokent &);

#endif // CPROVER_GOTO_PROGRAMS_FORMAT_STRINGS_H
