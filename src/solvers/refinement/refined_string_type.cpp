/********************************************************************\

Module: Type for string expressions used by the string solver.
        These string expressions contain a field `length`, of type
        `index_type`, a field `content` of type `content_type`.
        This module also defines functions to recognise the C and java
        string types.

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/refined_string_type.h>
#include <ansi-c/string_constant.h>
#include <util/cprover_prefix.h>

/*******************************************************************\

Constructor: refined_string_typet::refined_string_typet

     Inputs: type of characters

\*******************************************************************/

refined_string_typet::refined_string_typet(typet char_type)
{
  infinity_exprt infinite_index(refined_string_typet::index_type());
  array_typet char_array(char_type, infinite_index);
  components().emplace_back("length", refined_string_typet::index_type());
  components().emplace_back("content", char_array);
}

/*******************************************************************\

Function: refined_string_typet::is_c_string_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of C strings

\*******************************************************************/

bool refined_string_typet::is_c_string_type(const typet &type)
{
  return
    type.id()==ID_struct &&
    to_struct_type(type).get_tag()==CPROVER_PREFIX"string";
}

/*******************************************************************\

Function: refined_string_typet::is_java_string_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java string pointers

\*******************************************************************/

bool refined_string_typet::is_java_string_pointer_type(const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &subtype=pt.subtype();
    return is_java_string_type(subtype);
  }
  return false;
}

/*******************************************************************\

Function: refined_string_typet::is_java_string_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java string

\*******************************************************************/

bool refined_string_typet::is_java_string_type(const typet &type)
{
  if(type.id()==ID_symbol)
  {
    irep_idt tag=to_symbol_type(type).get_identifier();
    return tag=="java::java.lang.String";
  }
  else if(type.id()==ID_struct)
  {
    irep_idt tag=to_struct_type(type).get_tag();
    return tag=="java.lang.String";
  }
  return false;
}

/*******************************************************************\

Function: refined_string_typet::is_java_string_builder_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java string builder

\*******************************************************************/

bool refined_string_typet::is_java_string_builder_type(const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &subtype=pt.subtype();
    if(subtype.id()==ID_struct)
    {
      irep_idt tag=to_struct_type(subtype).get_tag();
      return tag=="java.lang.StringBuilder";
    }
  }
  return false;
}

/*******************************************************************\

Function: refined_string_typet::is_java_char_sequence_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java char sequence

\*******************************************************************/

bool refined_string_typet::is_java_char_sequence_type(const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &subtype=pt.subtype();
    if(subtype.id()==ID_struct)
    {
      const irep_idt &tag=to_struct_type(subtype).get_tag();
      return tag=="java.lang.CharSequence";
    }
  }
  return false;
}
