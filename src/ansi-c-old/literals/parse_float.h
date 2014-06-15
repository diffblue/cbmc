/*******************************************************************\

Module: ANSI-C Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_PARSE_FLOAT_H
#define CPROVER_ANSI_C_PARSE_FLOAT_H

#include <string>

#include <util/mp_arith.h>

void parse_float(
  const std::string &src,
  mp_integer &significand,
  mp_integer &exponent,
  unsigned &exponent_base, // 2 (hex) or 10
  bool &is_float,
  bool &is_long,
  bool &is_imaginary, // a gcc extension
  bool &is_decimal, // a gcc extension
  bool &is_float80, // a gcc extension
  bool &is_float128); // a gcc extension

#endif
