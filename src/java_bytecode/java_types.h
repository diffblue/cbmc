/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_TYPES_H
#define CPROVER_JAVA_BYTECODE_JAVA_TYPES_H

#include <util/type.h>
#include <util/std_types.h>

class java_class_typet:public class_typet
{
 public:
  const irep_idt &get_access() const
  {
    return get(ID_access);
  }

  void set_access(const irep_idt &access)
  {
    return set(ID_access, access);
  }
};

inline const java_class_typet &to_java_class_type(const typet &type)
{
  assert(type.id()==ID_struct);
  return static_cast<const java_class_typet &>(type);
}

inline java_class_typet &to_java_class_type(typet &type)
{
  assert(type.id()==ID_struct);
  return static_cast<java_class_typet &>(type);
}

typet java_int_type();
typet java_long_type();
typet java_short_type();
typet java_byte_type();
typet java_char_type();
typet java_float_type();
typet java_double_type();
typet java_boolean_type();
reference_typet java_reference_type(const typet &subtype);
reference_typet java_lang_object_type();
symbol_typet java_classname(const std::string &);

reference_typet java_array_type(const char subtype);

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

bool is_java_array_tag(const irep_idt& tag);

#endif // CPROVER_JAVA_BYTECODE_JAVA_TYPES_H
