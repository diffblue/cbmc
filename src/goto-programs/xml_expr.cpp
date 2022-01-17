/*******************************************************************\

Module: Expressions in XML

Author: Daniel Kroening

  Date: November 2005

\*******************************************************************/

/// \file
/// Expressions in XML

#include "xml_expr.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/fixedbv.h>
#include <util/ieee_float.h>
#include <util/invariant.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/xml.h>

xmlt xml(const typet &type, const namespacet &ns)
{
  xmlt result;

  if(type.id() == ID_unsignedbv)
  {
    result.name = "integer";
    result.set_attribute("width", to_unsignedbv_type(type).get_width());
  }
  else if(type.id() == ID_signedbv)
  {
    result.name = "integer";
    result.set_attribute("width", to_signedbv_type(type).get_width());
  }
  else if(type.id() == ID_floatbv)
  {
    result.name = "float";
    result.set_attribute("width", to_floatbv_type(type).get_width());
  }
  else if(type.id() == ID_bv)
  {
    result.name = "integer";
    result.set_attribute("width", to_bv_type(type).get_width());
  }
  else if(type.id() == ID_c_bit_field)
  {
    result.name = "integer";
    result.set_attribute("width", to_c_bit_field_type(type).get_width());
  }
  else if(type.id() == ID_c_enum_tag)
  {
    // we return the base type
    return xml(ns.follow_tag(to_c_enum_tag_type(type)).subtype(), ns);
  }
  else if(type.id() == ID_fixedbv)
  {
    result.name = "fixed";
    result.set_attribute("width", to_fixedbv_type(type).get_width());
  }
  else if(type.id() == ID_pointer)
  {
    result.name = "pointer";
    result.new_element("subtype").new_element() =
      xml(to_pointer_type(type).base_type(), ns);
  }
  else if(type.id() == ID_bool)
  {
    result.name = "boolean";
  }
  else if(type.id() == ID_array)
  {
    result.name = "array";
    result.new_element("subtype").new_element() =
      xml(to_array_type(type).element_type(), ns);
    result.new_element("size").new_element() =
      xml(to_array_type(type).size(), ns);
  }
  else if(type.id() == ID_vector)
  {
    result.name = "vector";
    result.new_element("subtype").new_element() =
      xml(to_vector_type(type).element_type(), ns);
    result.new_element("size").new_element() =
      xml(to_vector_type(type).size(), ns);
  }
  else if(type.id() == ID_struct)
  {
    result.name = "struct";
    const struct_typet::componentst &components =
      to_struct_type(type).components();
    for(const auto &component : components)
    {
      xmlt &e = result.new_element("member");
      e.set_attribute("name", id2string(component.get_name()));
      e.new_element("type").new_element() = xml(component.type(), ns);
    }
  }
  else if(type.id() == ID_struct_tag)
  {
    return xml(ns.follow_tag(to_struct_tag_type(type)), ns);
  }
  else if(type.id() == ID_union)
  {
    result.name = "union";
    const union_typet::componentst &components =
      to_union_type(type).components();
    for(const auto &component : components)
    {
      xmlt &e = result.new_element("member");
      e.set_attribute("name", id2string(component.get_name()));
      e.new_element("type").new_element() = xml(component.type(), ns);
    }
  }
  else if(type.id() == ID_union_tag)
  {
    return xml(ns.follow_tag(to_union_tag_type(type)), ns);
  }
  else
    result.name = "unknown";

  return result;
}

xmlt xml(const exprt &expr, const namespacet &ns)
{
  xmlt result;

  if(expr.id() == ID_constant)
  {
    const auto &constant_expr = to_constant_expr(expr);
    const auto &value = constant_expr.get_value();

    const typet &type = expr.type();

    if(
      type.id() == ID_unsignedbv || type.id() == ID_signedbv ||
      type.id() == ID_c_bit_field || type.id() == ID_c_bool)
    {
      mp_integer i = numeric_cast_v<mp_integer>(constant_expr);
      std::size_t width = to_bitvector_type(type).get_width();

      result.name = "integer";
      result.set_attribute("binary", integer2binary(i, width));
      result.set_attribute("width", width);

      const typet &underlying_type = type.id() == ID_c_bit_field
                                       ? to_c_bit_field_type(type).subtype()
                                       : type;

      bool is_signed = underlying_type.id() == ID_signedbv;

      std::string sig = is_signed ? "" : "unsigned ";

      if(type.id() == ID_c_bool)
        result.set_attribute("c_type", "_Bool");
      else if(width == config.ansi_c.char_width)
        result.set_attribute("c_type", sig + "char");
      else if(width == config.ansi_c.int_width)
        result.set_attribute("c_type", sig + "int");
      else if(width == config.ansi_c.short_int_width)
        result.set_attribute("c_type", sig + "short int");
      else if(width == config.ansi_c.long_int_width)
        result.set_attribute("c_type", sig + "long int");
      else if(width == config.ansi_c.long_long_int_width)
        result.set_attribute("c_type", sig + "long long int");

      result.data = integer2string(i);
    }
    else if(type.id() == ID_c_enum)
    {
      const auto width =
        to_bitvector_type(to_c_enum_type(type).subtype()).get_width();

      const auto integer_value = bvrep2integer(value, width, false);
      result.name = "integer";
      result.set_attribute("binary", integer2binary(integer_value, width));
      result.set_attribute("width", width);
      result.set_attribute("c_type", "enum");

      result.data = integer2string(integer_value);
    }
    else if(type.id() == ID_c_enum_tag)
    {
      constant_exprt tmp(
        constant_expr.get_value(), ns.follow_tag(to_c_enum_tag_type(type)));
      return xml(tmp, ns);
    }
    else if(type.id() == ID_bv)
    {
      result.name = "bitvector";
      result.set_attribute("binary", constant_expr.get_string(ID_value));
    }
    else if(type.id() == ID_fixedbv)
    {
      const auto width = to_fixedbv_type(type).get_width();
      result.name = "fixed";
      result.set_attribute("width", width);
      result.set_attribute(
        "binary", integer2binary(bvrep2integer(value, width, false), width));
      result.data = fixedbvt(constant_expr).to_ansi_c_string();
    }
    else if(type.id() == ID_floatbv)
    {
      const auto width = to_floatbv_type(type).get_width();
      result.name = "float";
      result.set_attribute("width", width);
      result.set_attribute(
        "binary", integer2binary(bvrep2integer(value, width, false), width));
      result.data = ieee_floatt(constant_expr).to_ansi_c_string();
    }
    else if(type.id() == ID_pointer)
    {
      const auto width = to_pointer_type(type).get_width();
      result.name = "pointer";
      result.set_attribute(
        "binary", integer2binary(bvrep2integer(value, width, false), width));
      if(constant_expr.get(ID_value) == ID_NULL)
        result.data = "NULL";
    }
    else if(type.id() == ID_bool)
    {
      result.name = "boolean";
      result.set_attribute("binary", constant_expr.is_true() ? "1" : "0");
      result.data = constant_expr.is_true() ? "TRUE" : "FALSE";
    }
    else
    {
      result.name = "unknown";
    }
  }
  else if(expr.id() == ID_array)
  {
    result.name = "array";

    unsigned index = 0;

    forall_operands(it, expr)
    {
      xmlt &e = result.new_element("element");
      e.set_attribute("index", index);
      e.new_element(xml(*it, ns));
      index++;
    }
  }
  else if(expr.id() == ID_struct)
  {
    result.name = "struct";

    const typet &type = ns.follow(expr.type());

    // these are expected to have a struct type
    if(type.id() == ID_struct)
    {
      const struct_typet &struct_type = to_struct_type(type);
      const struct_typet::componentst &components = struct_type.components();
      PRECONDITION(components.size() == expr.operands().size());

      for(unsigned m = 0; m < expr.operands().size(); m++)
      {
        xmlt &e = result.new_element("member");
        e.new_element() = xml(expr.operands()[m], ns);
        e.set_attribute("name", id2string(components[m].get_name()));
      }
    }
  }
  else if(expr.id() == ID_union)
  {
    const union_exprt &union_expr = to_union_expr(expr);
    result.name = "union";

    xmlt &e = result.new_element("member");
    e.new_element(xml(union_expr.op(), ns));
    e.set_attribute("member_name", id2string(union_expr.get_component_name()));
  }
  else
    result.name = "unknown";

  return result;
}
