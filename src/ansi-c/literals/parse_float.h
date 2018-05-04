/*******************************************************************\

Module: ANSI-C Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Conversion / Type Checking

#ifndef CPROVER_ANSI_C_LITERALS_PARSE_FLOAT_H
#define CPROVER_ANSI_C_LITERALS_PARSE_FLOAT_H

#include <string>

#include <util/mp_arith.h>

class parse_floatt
{
public:
  mp_integer significand, exponent;
  unsigned exponent_base; // 2 (hex) or 10

  bool is_float, is_long;

  // gcc extensions
  bool is_imaginary, is_decimal, is_float16,
       is_float32, is_float32x,
       is_float64, is_float64x,
       is_float80,
       is_float128, is_float128x;

  // parse!
  explicit parse_floatt(const std::string &);
};

#endif // CPROVER_ANSI_C_LITERALS_PARSE_FLOAT_H
