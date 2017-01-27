/*******************************************************************\

Module: Format String Parser

Author: CM Wintersteiger

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_FORMAT_STRINGS_H
#define CPROVER_GOTO_PROGRAMS_FORMAT_STRINGS_H

#include <string>
#include <list>

#include <util/expr.h>
#include <util/mp_arith.h>

class format_tokent
{
public:
  typedef enum { UNKNOWN,
                 TEXT,
                 INT, // d, i, o, u, x
                 FLOAT, // a, e, f, g
                 CHAR, // c
                 STRING, // s
                 POINTER // p
               } token_typet;

  typedef enum { ALTERNATE, ZERO_PAD, LEFT_ADJUST,
                 SIGNED_SPACE, SIGN, ASTERISK } flag_typet;

  typedef enum
  {
    LEN_undef, LEN_h, LEN_hh, LEN_l, LEN_ll,
    LEN_L, LEN_j, LEN_t
  } length_modifierst;

  typedef enum
  {
    SIGNED_undef, SIGNED_DEC, UNSIGNED_DEC,
    UNSIGNED_OCT, UNSIGNED_HEX
  } representationt;

  explicit format_tokent(token_typet _type)
    : type(_type),
      length_modifier(LEN_undef),
      representation(SIGNED_undef)
    { }
  format_tokent():
    type(UNKNOWN),
    length_modifier(LEN_undef),
    representation(SIGNED_undef)
    { }


  token_typet type;
  std::list<flag_typet> flags;
  mp_integer field_width;
  mp_integer precision;
  length_modifierst length_modifier;
  representationt representation;
  irep_idt value; // for text and pattern matching
};

class format_token_listt:public std::list<format_tokent>
{
};

format_token_listt parse_format_string(const std::string &);

typet get_type(const format_tokent &);

#endif // CPROVER_GOTO_PROGRAMS_FORMAT_STRINGS_H
