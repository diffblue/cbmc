/*******************************************************************\

Module: Expressions in JSON

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Expressions in JSON

#include "json_expr.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/fixedbv.h>
#include <util/identifier.h>
#include <util/ieee_float.h>
#include <util/invariant.h>
#include <util/json.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>

#include <langapi/language.h>
#include <langapi/mode.h>

#include <memory>

static exprt simplify_json_expr(const exprt &src)
{
  if(src.id() == ID_typecast)
  {
    return simplify_json_expr(to_typecast_expr(src).op());
  }
  else if(src.id() == ID_address_of)
  {
    const exprt &object = skip_typecast(to_address_of_expr(src).object());

    if(object.id() == ID_symbol)
    {
      // simplify expressions of the form &symbol
      return simplify_json_expr(object);
    }
    else if(
      object.id() == ID_member &&
      id2string(to_member_expr(object).get_component_name()).find("@") !=
      std::string::npos)
    {
      // simplify expressions of the form &member(object, @class_identifier)
      return simplify_json_expr(object);
    }
    else if(
      object.id() == ID_index && to_index_expr(object).index().is_constant() &&
      to_constant_expr(to_index_expr(object).index()).value_is_zero_string())
    {
      // simplify expressions of the form  &array[0]
      return simplify_json_expr(to_index_expr(object).array());
    }
  }
  else if(
    src.id() == ID_member &&
    id2string(to_member_expr(src).get_component_name()).find("@") !=
      std::string::npos)
  {
    // simplify expressions of the form  member_expr(object, @class_identifier)
    return simplify_json_expr(to_member_expr(src).struct_op());
  }

  return src;
}

/// Output a CBMC type in json.
/// The `mode` argument is used to correctly report types.
/// \param type: a type
/// \param ns: a namespace
/// \param mode: language in which the code was written
/// \return a json object
json_objectt json(const typet &type, const namespacet &ns, const irep_idt &mode)
{
  json_objectt result;

  if(type.id() == ID_unsignedbv)
  {
    result["name"] = json_stringt("integer");
    result["width"] =
      json_numbert(std::to_string(to_unsignedbv_type(type).get_width()));
  }
  else if(type.id() == ID_signedbv)
  {
    result["name"] = json_stringt("integer");
    result["width"] =
      json_numbert(std::to_string(to_signedbv_type(type).get_width()));
  }
  else if(type.id() == ID_floatbv)
  {
    result["name"] = json_stringt("float");
    result["width"] =
      json_numbert(std::to_string(to_floatbv_type(type).get_width()));
  }
  else if(type.id() == ID_bv)
  {
    result["name"] = json_stringt("integer");
    result["width"] =
      json_numbert(std::to_string(to_bv_type(type).get_width()));
  }
  else if(type.id() == ID_c_bit_field)
  {
    result["name"] = json_stringt("integer");
    result["width"] =
      json_numbert(std::to_string(to_c_bit_field_type(type).get_width()));
  }
  else if(type.id() == ID_c_enum_tag)
  {
    // we return the underlying type
    return json(
      ns.follow_tag(to_c_enum_tag_type(type)).underlying_type(), ns, mode);
  }
  else if(type.id() == ID_fixedbv)
  {
    result["name"] = json_stringt("fixed");
    result["width"] =
      json_numbert(std::to_string(to_fixedbv_type(type).get_width()));
  }
  else if(type.id() == ID_pointer)
  {
    result["name"] = json_stringt("pointer");
    result["subtype"] = json(to_pointer_type(type).base_type(), ns, mode);
  }
  else if(type.id() == ID_bool)
  {
    result["name"] = json_stringt("boolean");
  }
  else if(type.id() == ID_array)
  {
    result["name"] = json_stringt("array");
    result["subtype"] = json(to_array_type(type).element_type(), ns, mode);
    result["size"] = json(to_array_type(type).size(), ns, mode);
  }
  else if(type.id() == ID_vector)
  {
    result["name"] = json_stringt("vector");
    result["subtype"] = json(to_vector_type(type).element_type(), ns, mode);
    result["size"] = json(to_vector_type(type).size(), ns, mode);
  }
  else if(type.id() == ID_struct)
  {
    result["name"] = json_stringt("struct");
    json_arrayt &members = result["members"].make_array();
    const struct_typet::componentst &components =
      to_struct_type(type).components();
    for(const auto &component : components)
    {
      json_objectt e{{"name", json_stringt(component.get_name())},
                     {"type", json(component.type(), ns, mode)}};
      members.push_back(std::move(e));
    }
  }
  else if(type.id() == ID_struct_tag)
  {
    return json(ns.follow_tag(to_struct_tag_type(type)), ns, mode);
  }
  else if(type.id() == ID_union)
  {
    result["name"] = json_stringt("union");
    json_arrayt &members = result["members"].make_array();
    const union_typet::componentst &components =
      to_union_type(type).components();
    for(const auto &component : components)
    {
      json_objectt e{{"name", json_stringt(component.get_name())},
                     {"type", json(component.type(), ns, mode)}};
      members.push_back(std::move(e));
    }
  }
  else if(type.id() == ID_union_tag)
  {
    return json(ns.follow_tag(to_union_tag_type(type)), ns, mode);
  }
  else
    result["name"] = json_stringt("unknown");

  return result;
}

static std::string binary(const constant_exprt &src)
{
  std::size_t width;
  if(src.type().id() == ID_c_enum)
    width = to_bitvector_type(to_c_enum_type(src.type()).underlying_type())
              .get_width();
  else
    width = to_bitvector_type(src.type()).get_width();
  const auto int_val = bvrep2integer(src.get_value(), width, false);
  return integer2binary(int_val, width);
}

/// Output a CBMC expression in json.
/// The mode is used to correctly report types.
/// \param expr: an expression
/// \param ns: a namespace
/// \param mode: language in which the code was written
/// \return a json object
json_objectt json(const exprt &expr, const namespacet &ns, const irep_idt &mode)
{
  json_objectt result;

  if(expr.is_constant())
  {
    const constant_exprt &constant_expr = to_constant_expr(expr);

    const typet &type = expr.type();

    std::unique_ptr<languaget> lang;
    if(mode != ID_unknown)
      lang = std::unique_ptr<languaget>(get_language_from_mode(mode));
    if(!lang)
      lang = std::unique_ptr<languaget>(get_default_language());

    const typet &underlying_type =
      type.id() == ID_c_bit_field ? to_c_bit_field_type(type).underlying_type()
                                  : type;

    std::string type_string;
    bool error = lang->from_type(underlying_type, type_string, ns);
    CHECK_RETURN(!error);

    std::string value_string;
    lang->from_expr(expr, value_string, ns);

    if(
      type.id() == ID_unsignedbv || type.id() == ID_signedbv ||
      type.id() == ID_c_bit_field || type.id() == ID_c_bool)
    {
      std::size_t width = to_bitvector_type(type).get_width();

      result["name"] = json_stringt("integer");
      result["binary"] = json_stringt(binary(constant_expr));
      result["width"] = json_numbert(std::to_string(width));
      result["type"] = json_stringt(type_string);
      result["data"] = json_stringt(value_string);
    }
    else if(type.id() == ID_c_enum)
    {
      result["name"] = json_stringt("integer");
      result["binary"] = json_stringt(binary(constant_expr));
      result["width"] = json_numbert(std::to_string(
        to_bitvector_type(to_c_enum_type(type).underlying_type()).get_width()));
      result["type"] = json_stringt("enum");
      result["data"] = json_stringt(value_string);
    }
    else if(type.id() == ID_c_enum_tag)
    {
      constant_exprt tmp(
        constant_expr.get_value(), ns.follow_tag(to_c_enum_tag_type(type)));
      return json(tmp, ns, mode);
    }
    else if(type.id() == ID_bv)
    {
      result["name"] = json_stringt("bitvector");
      result["binary"] = json_stringt(binary(constant_expr));
    }
    else if(type.id() == ID_fixedbv)
    {
      result["name"] = json_stringt("fixed");
      result["width"] =
        json_numbert(std::to_string(to_bitvector_type(type).get_width()));
      result["binary"] = json_stringt(binary(constant_expr));
      result["data"] = json_stringt(fixedbvt(constant_expr).to_ansi_c_string());
    }
    else if(type.id() == ID_floatbv)
    {
      result["name"] = json_stringt("float");
      result["width"] =
        json_numbert(std::to_string(to_bitvector_type(type).get_width()));
      result["binary"] = json_stringt(binary(constant_expr));
      result["data"] =
        json_stringt(ieee_floatt(constant_expr).to_ansi_c_string());
    }
    else if(type.id() == ID_pointer)
    {
      result["name"] = json_stringt("pointer");
      result["type"] = json_stringt(type_string);
      if(constant_expr.get_value() == ID_NULL)
        result["data"] = json_stringt(value_string);
    }
    else if(type.id() == ID_bool)
    {
      result["name"] = json_stringt("boolean");
      result["binary"] =
        json_stringt(to_constant_expr(expr).is_true() ? "1" : "0");
      result["data"] = jsont::json_boolean(to_constant_expr(expr).is_true());
    }
    else if(type.id() == ID_string)
    {
      result["name"] = json_stringt("string");
      result["data"] = json_stringt(constant_expr.get_value());
    }
    else
    {
      result["name"] = json_stringt("unknown");
    }
  }
  else if(expr.id() == ID_annotated_pointer_constant)
  {
    const annotated_pointer_constant_exprt &c =
      to_annotated_pointer_constant_expr(expr);
    exprt simpl_expr = simplify_json_expr(c.symbolic_pointer());

    if(simpl_expr.id() == ID_symbol)
    {
      result["name"] = json_stringt("pointer");

      const typet &type = expr.type();

      std::unique_ptr<languaget> lang;
      if(mode != ID_unknown)
        lang = std::unique_ptr<languaget>(get_language_from_mode(mode));
      if(!lang)
        lang = std::unique_ptr<languaget>(get_default_language());

      const typet &underlying_type =
        type.id() == ID_c_bit_field
          ? to_c_bit_field_type(type).underlying_type()
          : type;

      std::string type_string;
      bool error = lang->from_type(underlying_type, type_string, ns);
      CHECK_RETURN(!error);
      result["type"] = json_stringt(type_string);

      const irep_idt &ptr_id = to_symbol_expr(simpl_expr).get_identifier();
      identifiert identifier(id2string(ptr_id));
      DATA_INVARIANT(
        !identifier.components.empty(),
        "pointer identifier should have non-empty components");
      result["data"] = json_stringt(identifier.components.back());
    }
    else if(simpl_expr.is_constant())
      return json(simpl_expr, ns, mode);
    else
      result["name"] = json_stringt("unknown");
  }
  else if(expr.id() == ID_array)
  {
    result["name"] = json_stringt("array");
    json_arrayt &elements = result["elements"].make_array();

    std::size_t index = 0;

    for(const auto &op : expr.operands())
    {
      json_objectt e{
        {"index", json_numbert(std::to_string(index))},
        {"value", json(op, ns, mode)}};
      elements.push_back(std::move(e));
      index++;
    }
  }
  else if(expr.id() == ID_struct)
  {
    result["name"] = json_stringt("struct");

    const struct_typet &struct_type =
      expr.type().id() == ID_struct_tag
        ? ns.follow_tag(to_struct_tag_type(expr.type()))
        : to_struct_type(expr.type());
    const struct_typet::componentst &components = struct_type.components();
    DATA_INVARIANT(
      components.size() == expr.operands().size(),
      "number of struct components should match with its type");

    json_arrayt &members = result["members"].make_array();
    for(std::size_t m = 0; m < expr.operands().size(); m++)
    {
      json_objectt e{
        {"value", json(expr.operands()[m], ns, mode)},
        {"name", json_stringt(components[m].get_name())}};
      members.push_back(std::move(e));
    }
  }
  else if(expr.id() == ID_union)
  {
    result["name"] = json_stringt("union");

    const union_exprt &union_expr = to_union_expr(expr);
    result["member"] =
      json_objectt({{"value", json(union_expr.op(), ns, mode)},
                    {"name", json_stringt(union_expr.get_component_name())}});
  }
  else
    result["name"] = json_stringt("unknown");

  return result;
}
