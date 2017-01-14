/** -*- C++ -*- *****************************************************\

Module: Type of string expressions for PASS algorithm
        (see the PASS paper at HVC'13)

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/refined_string_type.h>
#include <ansi-c/string_constant.h>

refined_string_typet::refined_string_typet(unsignedbv_typet char_type) : struct_typet() {
  components().resize(2);
  components()[0].set_name("length");
  components()[0].set_pretty_name("length");
  components()[0].type()=refined_string_typet::index_type();

  array_typet char_array(char_type,infinity_exprt(refined_string_typet::index_type()));
  components()[1].set_name("content");
  components()[1].set_pretty_name("content");
  components()[1].type()=char_array;
}

bool refined_string_typet::is_c_string_type(const typet &type)
{
  if (type.id() == ID_struct) {
    irep_idt tag = to_struct_type(type).get_tag();
    return (tag == irep_idt("__CPROVER_string"));
  } else return false;
}

bool refined_string_typet::is_java_string_type(const typet &type)
{
  if(type.id() == ID_pointer) {
    pointer_typet pt = to_pointer_type(type);
    typet subtype = pt.subtype();
    return is_java_deref_string_type(subtype);
  } else return false;
}

bool refined_string_typet::is_java_deref_string_type(const typet &type)
{
  if(type.id() == ID_struct) {
    irep_idt tag = to_struct_type(type).get_tag();
    return (tag == irep_idt("java.lang.String"));
  } 
  else return false;
}

bool refined_string_typet::is_java_string_builder_type(const typet &type)
{
  if(type.id() == ID_pointer) {
    pointer_typet pt = to_pointer_type(type);
    typet subtype = pt.subtype();
    if(subtype.id() == ID_struct) {
      irep_idt tag = to_struct_type(subtype).get_tag();
      return (tag == irep_idt("java.lang.StringBuilder"));
    } 
    else return false;
  } else return false;
}

bool refined_string_typet::is_java_char_sequence_type(const typet &type)
{
  if(type.id() == ID_pointer) {
    pointer_typet pt = to_pointer_type(type);
    typet subtype = pt.subtype();
    if(subtype.id() == ID_struct) {
      irep_idt tag = to_struct_type(subtype).get_tag();
      return (tag == irep_idt("java.lang.CharSequence"));
    } 
    else return false;
  } else return false;
}

