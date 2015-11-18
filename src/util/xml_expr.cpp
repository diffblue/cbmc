/*******************************************************************\

Module: Expressions in XML

Author: Daniel Kroening

  Date: November 2005

\*******************************************************************/

#include "namespace.h"
#include "expr.h"
#include "xml.h"
#include "arith_tools.h"
#include "ieee_float.h"
#include "fixedbv.h"
#include "std_expr.h"
#include "config.h"

#include "xml_expr.h"

/*******************************************************************\

Function: xml

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

xmlt xml(const source_locationt &location)
{
  xmlt result;

  result.name="location";
  
  if(!location.get_file().empty())
    result.set_attribute("file", id2string(location.get_file()));

  if(!location.get_line().empty())
    result.set_attribute("line", id2string(location.get_line()));

  if(!location.get_column().empty())
    result.set_attribute("column", id2string(location.get_column()));

  if(!location.get_function().empty())
    result.set_attribute("function", id2string(location.get_function()));
  
  return result;
}

/*******************************************************************\

Function: xml

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

xmlt xml(
  const typet &type,
  const namespacet &ns)
{
  if(type.id()==ID_symbol)
    return xml(ns.follow(type), ns);

  xmlt result;

  if(type.id()==ID_unsignedbv)
  {
    result.name="integer";
    result.set_attribute("width", to_unsignedbv_type(type).get_width());
  }
  else if(type.id()==ID_signedbv)
  {
    result.name="integer";
    result.set_attribute("width", to_signedbv_type(type).get_width());
  }
  else if(type.id()==ID_floatbv)
  {
    result.name="float";
    result.set_attribute("width", to_floatbv_type(type).get_width());
  }
  else if(type.id()==ID_bv)
  {
    result.name="integer";
    result.set_attribute("width", to_bv_type(type).get_width());
  }
  else if(type.id()==ID_c_bit_field)
  {
    result.name="integer";
    result.set_attribute("width", to_c_bit_field_type(type).get_width());
  }
  else if(type.id()==ID_c_enum_tag)
  {
    // we return the base type
    return xml(ns.follow_tag(to_c_enum_tag_type(type)).subtype(), ns);
  }
  else if(type.id()==ID_fixedbv)
  {
    result.name="fixed";
    result.set_attribute("width", to_fixedbv_type(type).get_width());
  }
  else if(type.id()==ID_pointer)
  {
    result.name="pointer";
    result.new_element("subtype").new_element()=xml(type.subtype(), ns);
  }
  else if(type.id()==ID_bool)
  {
    result.name="boolean";
  }
  else if(type.id()==ID_array)
  {
    result.name="array";
    result.new_element("subtype").new_element()=xml(type.subtype(), ns);
  }
  else if(type.id()==ID_vector)
  {
    result.name="vector";
    result.new_element("subtype").new_element()=xml(type.subtype(), ns);
    result.new_element("size").new_element()=xml(to_vector_type(type).size(), ns);
  }
  else if(type.id()==ID_struct)
  {
    result.name="struct";
    const struct_typet::componentst &components=
      to_struct_type(type).components();
    for(struct_typet::componentst::const_iterator
        it=components.begin(); it!=components.end(); it++)
    {
      xmlt &e=result.new_element("member");
      e.set_attribute("name", id2string(it->get_name()));
      e.new_element("type").new_element()=xml(it->type(), ns);
    }
  }
  else if(type.id()==ID_union)
  {
    result.name="union";
    const union_typet::componentst &components=
      to_union_type(type).components();
    for(union_typet::componentst::const_iterator
        it=components.begin(); it!=components.end(); it++)
    {
      xmlt &e=result.new_element("member");
      e.set_attribute("name", id2string(it->get_name()));
      e.new_element("type").new_element()=xml(it->type(), ns);
    }
  }
  else
    result.name="unknown";

  return result;
}

/*******************************************************************\

Function: xml

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

xmlt xml(
  const exprt &expr,
  const namespacet &ns)
{
  xmlt result;
  
  const typet &type=ns.follow(expr.type());

  if(expr.id()==ID_constant)
  {
    if(type.id()==ID_unsignedbv ||
       type.id()==ID_signedbv ||
       type.id()==ID_c_bit_field)
    {
      unsigned width=to_bitvector_type(type).get_width();
    
      result.name="integer";
      result.set_attribute("binary", expr.get_string(ID_value));
      result.set_attribute("width", width);
      
      const typet &underlying_type=
        type.id()==ID_c_bit_field?type.subtype():
        type;

      bool is_signed=underlying_type.id()==ID_signedbv;
        
      std::string sig=is_signed?"":"unsigned ";

      if(width==config.ansi_c.char_width)
        result.set_attribute("c_type", sig+"char");
      else if(width==config.ansi_c.int_width)
        result.set_attribute("c_type", sig+"int");
      else if(width==config.ansi_c.short_int_width)
        result.set_attribute("c_type", sig+"short int");
      else if(width==config.ansi_c.long_int_width)
        result.set_attribute("c_type", sig+"long int");
      else if(width==config.ansi_c.long_long_int_width)
        result.set_attribute("c_type", sig+"long long int");

      mp_integer i;
      if(!to_integer(expr, i))
        result.data=integer2string(i);
    }
    else if(type.id()==ID_c_enum)
    {
      result.name="integer";
      result.set_attribute("binary", expr.get_string(ID_value));
      result.set_attribute("width", type.subtype().get_string(ID_width));
      result.set_attribute("c_type", "enum");

      mp_integer i;
      if(!to_integer(expr, i))
        result.data=integer2string(i);
    }
    else if(type.id()==ID_c_enum_tag)
    {
      constant_exprt tmp;
      tmp.type()=ns.follow_tag(to_c_enum_tag_type(type));
      tmp.set_value(to_constant_expr(expr).get_value());
      return xml(tmp, ns);
    }
    else if(type.id()==ID_bv)
    {
      result.name="bitvector";
      result.set_attribute("binary", expr.get_string(ID_value));
    }
    else if(type.id()==ID_fixedbv)
    {
      result.name="fixed";
      result.set_attribute("width", type.get_string(ID_width));
      result.set_attribute("binary", expr.get_string(ID_value));
      result.data=fixedbvt(to_constant_expr(expr)).to_ansi_c_string();
    }
    else if(type.id()==ID_floatbv)
    {
      result.name="float";
      result.set_attribute("width", type.get_string(ID_width));
      result.set_attribute("binary", expr.get_string(ID_value));
      result.data=ieee_floatt(to_constant_expr(expr)).to_ansi_c_string();
    }
    else if(type.id()==ID_pointer)
    {
      result.name="pointer";
      result.set_attribute("binary", expr.get_string(ID_value));
      if(expr.get(ID_value)==ID_NULL)
        result.data="NULL";
    }
    else if(type.id()==ID_bool)
    {
      result.name="boolean";
      result.set_attribute("binary", expr.is_true()?"1":"0");
      result.data=expr.is_true()?"TRUE":"FALSE";
    }
    else
    {
      result.name="unknown";
    }
  }
  else if(expr.id()==ID_array)
  {
    result.name="array";
    
    unsigned index=0;
    
    forall_operands(it, expr)
    {
      xmlt &e=result.new_element("element");
      e.set_attribute("index", index);
      e.new_element(xml(*it, ns));
      index++;
    }
  }
  else if(expr.id()==ID_struct)
  {
    result.name="struct";
    
    // these are expected to have a struct type
    if(type.id()==ID_struct)
    {
      const struct_typet &struct_type=to_struct_type(type);
      const struct_typet::componentst &components=struct_type.components();
      assert(components.size()==expr.operands().size());

      for(unsigned m=0; m<expr.operands().size(); m++)
      {
        xmlt &e=result.new_element("member");
        e.new_element()=xml(expr.operands()[m], ns);
        e.set_attribute("name", id2string(components[m].get_name()));
      }
    }
  }
  else if(expr.id()==ID_union)
  { 
    result.name="union";
    
    assert(expr.operands().size()==1);
    
    xmlt &e=result.new_element("member");
    e.new_element(xml(expr.op0(), ns));
    e.set_attribute("member_name",
      id2string(to_union_expr(expr).get_component_name()));
  }
  else
    result.name="unknown";

  return result;
}

