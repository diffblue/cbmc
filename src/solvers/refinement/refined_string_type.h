/** -*- C++ -*- *****************************************************\

Module: Type of string expressions for PASS algorithm
        (see the PASS paper at HVC'13)

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#ifndef CPROVER_SOLVER_REFINED_STRING_TYPE_H
#define CPROVER_SOLVER_REFINED_STRING_TYPE_H

#include <util/std_types.h>
#include <util/std_expr.h>

#define STRING_SOLVER_INDEX_WIDTH 32
#define STRING_SOLVER_CHAR_WIDTH 8
#define JAVA_STRING_SOLVER_CHAR_WIDTH 16

// Internal type used for string refinement
class refined_string_typet : public struct_typet {
public:
  refined_string_typet(unsignedbv_typet char_type);

  // Type for the content (list of characters) of a string
  inline array_typet get_content_type() 
  { return to_array_type((to_struct_type(*this)).components()[1].type());}

  // Types used in this refinement
  static inline unsignedbv_typet char_type() { return unsignedbv_typet(STRING_SOLVER_CHAR_WIDTH);}

  static inline unsignedbv_typet java_char_type() { return unsignedbv_typet(JAVA_STRING_SOLVER_CHAR_WIDTH);}

  static inline signedbv_typet index_type() { return signedbv_typet(STRING_SOLVER_INDEX_WIDTH);}

  static inline exprt index_zero() { return constant_exprt(integer2binary(0, STRING_SOLVER_INDEX_WIDTH), index_type());}

  // For C the unrefined string type is __CPROVER_string, for java it is a 
  // pointer to a strict with tag java.lang.String

  static bool is_c_string_type(const typet & type);

  static bool is_java_string_type(const typet & type);

  static bool is_java_deref_string_type(const typet & type);

  static bool is_java_string_builder_type(const typet & type);

  static bool is_java_char_sequence_type(const typet & type);

  static inline unsignedbv_typet get_char_type(const exprt & expr) {
    if(is_c_string_type(expr.type())) return char_type();
    else return java_char_type();
  }

  static inline bool is_unrefined_string_type(const typet & type)
  {  return (is_c_string_type(type) 
          || is_java_string_type(type) 
          || is_java_string_builder_type(type)
          || is_java_char_sequence_type(type)
	     ); }

  static inline bool is_unrefined_string(const exprt & expr)
  {  return (is_unrefined_string_type(expr.type())); }

  static inline constant_exprt index_of_int(int i) 
  {  return constant_exprt(integer2binary(i, STRING_SOLVER_INDEX_WIDTH), 
			   index_type()); }

};


#endif
