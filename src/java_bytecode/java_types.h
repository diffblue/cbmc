/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_TYPES_H
#define CPROVER_JAVA_TYPES_H

#include <util/type.h>

typet java_int_type();
typet java_long_type();
typet java_short_type();
typet java_byte_type();
typet java_char_type();
typet java_float_type();
typet java_double_type();
typet java_boolean_type();
typet java_reference_type(const typet &subtype);
typet java_array_type(const typet &subtype);

// i  integer
// l  long
// s  short
// b  byte
// c  character
// f  float
// d  double
// z  boolean
// a  reference

typet java_type(char t);
typet java_type_from_string(const std::string &);

#endif
