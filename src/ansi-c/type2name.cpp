/*******************************************************************\

Module: Type Naming for C

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <ctype.h>

#include <i2string.h>
#include <std_types.h>

#include "type2name.h"

/*******************************************************************\

Function: type2name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string type2name(const typet &type)
{
  std::string result;
  
  // qualifiers first
  if(type.get_bool(ID_C_constant))
    result+="c";

  if(type.get_bool(ID_C_restricted))
    result+="r";

  if(type.get_bool(ID_C_volatile))
    result+="v";

  if(type.id()==irep_idt())
    throw "Empty type encountered.";
  else if(type.id()==ID_empty)
    result+="V";   
  else if(type.id()==ID_signedbv)
    result+="S" + type.get_string(ID_width);
  else if(type.id()==ID_unsignedbv)
    result+="U" + type.get_string(ID_width);
  else if(type.id()==ID_bool) 
    result+="B";
  else if(type.id()==ID_integer) 
    result+="I";
  else if(type.id()==ID_real) 
    result+="R";
  else if(type.id()==ID_complex) 
    result+="C";
  else if(type.id()==ID_floatbv) 
    result+="F" + type.get_string(ID_width);
  else if(type.id()==ID_fixedbv) 
    result+="X" + type.get_string(ID_width);
  else if(type.id()==ID_natural)
    result+="N";
  else if(type.id()==ID_pointer)
    result+="*";
  else if(type.id()==ID_reference)
    result+="&";
  else if(type.id()==ID_code)
  {
    const code_typet &t=to_code_type(type);
    const code_typet::argumentst arguments=t.arguments();
    result+="P(";

    for(code_typet::argumentst::const_iterator
        it=arguments.begin();
        it!=arguments.end();
        it++)
    {      
      if(it!=arguments.begin()) result+="|";
      result+=type2name(it->type());
    }

    if(t.has_ellipsis())
    {
      if(!arguments.empty()) result+="|";
      result+="...";
    }

    result+=")->";
    result+=type2name(t.return_type());
  }
  else if(type.id()==ID_array)
  {
    const array_typet &t=to_array_type(type);
    if(t.size().is_nil())
      result+="ARR?";
    else
      result+="ARR"+t.size().get_string(ID_value);
  }
  else if(type.id()==ID_symbol)
  {
    result+="SYM#"+type.get_string(ID_identifier)+"#";
  }
  else if(type.id()==ID_struct || 
          type.id()==ID_union)
  {
    if(type.id()==ID_struct) result+="ST";
    if(type.id()==ID_union) result+="UN";
    const struct_union_typet &t=to_struct_union_type(type);
    const struct_union_typet::componentst &components = t.components();
    result+="[";
    for(struct_union_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {            
      if(it!=components.begin()) result+="|";
      result+=type2name(it->type());
      result+="'"+it->get_string(ID_name)+"'|";
    }
    result+="]";
  }
  else if(type.id()==ID_incomplete_struct)
    result +="ST?";
  else if(type.id()==ID_incomplete_union)
    result +="UN?";
  else if(type.id()==ID_c_enum)
    result +="EN"+type.get_string(ID_width);
  else if(type.id()==ID_incomplete_c_enum)
    result +="EN?";
  else if(type.id()==ID_c_bitfield)
    result+="BF"+type.get_string(ID_size);
  else if(type.id()==ID_vector)
    result+="VEC"+type.get_string(ID_size);
  else
    throw (std::string("Unknown type '") + 
           type.id_string() + 
           "' encountered."); 
    
  if(type.has_subtype())
  {
    result+="{";
    result+=type2name(type.subtype());    
    result+="}";
  }

  if(type.has_subtypes())
  {
    result+="$";
    forall_subtypes(it, type)
    {      
      result+=type2name(*it);
      result+="|";      
    }
    result.resize(result.size()-1);
    result+="$";
  }
  
  return result;
}

