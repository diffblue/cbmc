/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_TYPES_H
#define CPROVER_JAVA_TYPES_H

#include <util/type.h>
#include <util/std_types.h>

typet java_int_type();
typet java_long_type();
typet java_short_type();
typet java_byte_type();
typet java_char_type();
typet java_float_type();
typet java_double_type();
typet java_boolean_type();
typet java_reference_type(const typet &subtype);

pointer_typet java_array_type(const typet &subtype, unsigned dimension);
pointer_typet java_array_type(const char subtype);

bool is_reference_type(char t);

// i  integer
// l  long
// s  short
// b  byte
// c  character
// f  float
// d  double
// z  boolean
// a  reference

typet java_type_from_char(char t);
typet java_type_from_string(const std::string &);
char java_char_from_type(const typet &type);

typet java_bytecode_promotion(const typet &);
exprt java_bytecode_promotion(const exprt &);

#endif
