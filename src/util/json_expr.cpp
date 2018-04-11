/*******************************************************************\

Module: Expressions in JSON

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Expressions in JSON

#include "json_expr.h"

#include "namespace.h"
#include "expr.h"
#include "json.h"
#include "arith_tools.h"
#include "ieee_float.h"
#include "fixedbv.h"
#include "std_expr.h"
#include "config.h"
#include "identifier.h"
#include "invariant.h"
#include "format.h"
#include "format_type.h"
#include "format_expr.h"
#include "format_constant.h"

#include <memory>
#include <sstream>

static exprt simplify_json_expr(
  const exprt &src,
  const namespacet &ns)
{
  if(src.id()==ID_constant)
  {
    const typet &type=ns.follow(src.type());

    if(type.id()==ID_pointer)
    {
      const irep_idt &value=to_constant_expr(src).get_value();

      if(value!=ID_NULL &&
         (value!=std::string(value.size(), '0') ||
          !config.ansi_c.NULL_is_zero) &&
         src.operands().size()==1 &&
         src.op0().id()!=ID_constant)
        // try to simplify the constant pointer
        return simplify_json_expr(src.op0(), ns);
    }
  }
  else if(src.id()==ID_address_of &&
          src.operands().size()==1 &&
          src.op0().id()==ID_member &&
          id2string(to_member_expr(
            src.op0()).get_component_name()).find("@")!=std::string::npos)
  {
    // simplify expressions of the form &member_expr(object, @class_identifier)
    return simplify_json_expr(src.op0(), ns);
  }
  else if(src.id()==ID_address_of &&
          src.operands().size()==1 &&
          src.op0().id()==ID_index &&
          to_index_expr(src.op0()).index().id()==ID_constant &&
          to_constant_expr(
            to_index_expr(src.op0()).index()).value_is_zero_string())
  {
    // simplify expressions of the form  &array[0]
    return simplify_json_expr(to_index_expr(src.op0()).array(), ns);
  }
  else if(src.id()==ID_member &&
          src.operands().size()==1 &&
          id2string(
            to_member_expr(src).get_component_name())
              .find("@")!=std::string::npos)
  {
    // simplify expressions of the form  member_expr(object, @class_identifier)
    return simplify_json_expr(src.op0(), ns);
  }

  return src;
}

json_objectt json_exprt::operator()(const source_locationt &location)
{
  json_objectt result;

  if(!location.get_working_directory().empty())
    result["workingDirectory"]=
      json_stringt(id2string(location.get_working_directory()));

  if(!location.get_file().empty())
    result["file"]=json_stringt(id2string(location.get_file()));

  if(!location.get_line().empty())
    result["line"]=json_stringt(id2string(location.get_line()));

  if(!location.get_column().empty())
    result["column"]=json_stringt(id2string(location.get_column()));

  if(!location.get_function().empty())
    result["function"]=json_stringt(id2string(location.get_function()));

  return result;
}

/// Output a CBMC type in json.
/// \param type: a type
/// \param ns: a namespace
/// \return a json object
json_objectt json_exprt::operator()(
  const typet &type,
  const namespacet &ns)
{
  if(type.id()==ID_symbol)
    return (*this)(ns.follow(type), ns);

  json_objectt result;

  if(type.id()==ID_unsignedbv)
  {
    result["name"]=json_stringt("integer");
    result["width"]=
      json_numbert(std::to_string(to_unsignedbv_type(type).get_width()));
  }
  else if(type.id()==ID_signedbv)
  {
    result["name"]=json_stringt("integer");
    result["width"]=
      json_numbert(std::to_string(to_signedbv_type(type).get_width()));
  }
  else if(type.id()==ID_floatbv)
  {
    result["name"]=json_stringt("float");
    result["width"]=
      json_numbert(std::to_string(to_floatbv_type(type).get_width()));
  }
  else if(type.id()==ID_bv)
  {
    result["name"]=json_stringt("integer");
    result["width"]=json_numbert(std::to_string(to_bv_type(type).get_width()));
  }
  else if(type.id()==ID_c_bit_field)
  {
    result["name"]=json_stringt("integer");
    result["width"]=
      json_numbert(std::to_string(to_c_bit_field_type(type).get_width()));
  }
  else if(type.id()==ID_c_enum_tag)
  {
    // we return the base type
    return (*this)(ns.follow_tag(to_c_enum_tag_type(type)).subtype(), ns);
  }
  else if(type.id()==ID_fixedbv)
  {
    result["name"]=json_stringt("fixed");
    result["width"]=
      json_numbert(std::to_string(to_fixedbv_type(type).get_width()));
  }
  else if(type.id()==ID_pointer)
  {
    result["name"]=json_stringt("pointer");
    result["subtype"] = (*this)(type.subtype(), ns);
  }
  else if(type.id()==ID_bool)
  {
    result["name"]=json_stringt("boolean");
  }
  else if(type.id()==ID_array)
  {
    result["name"]=json_stringt("array");
    result["subtype"] = (*this)(type.subtype(), ns);
  }
  else if(type.id()==ID_vector)
  {
    result["name"]=json_stringt("vector");
    result["subtype"] = (*this)(type.subtype(), ns);
    result["size"] = (*this)(to_vector_type(type).size(), ns);
  }
  else if(type.id()==ID_struct)
  {
    result["name"]=json_stringt("struct");
    json_arrayt &members=result["members"].make_array();
    const struct_typet::componentst &components=
      to_struct_type(type).components();
    for(const auto &component : components)
    {
      json_objectt &e=members.push_back().make_object();
      e["name"]=json_stringt(id2string(component.get_name()));
      e["type"] = (*this)(component.type(), ns);
    }
  }
  else if(type.id()==ID_union)
  {
    result["name"]=json_stringt("union");
    json_arrayt &members=result["members"].make_array();
    const union_typet::componentst &components=
      to_union_type(type).components();
    for(const auto &component : components)
    {
      json_objectt &e=members.push_back().make_object();
      e["name"]=json_stringt(id2string(component.get_name()));
      e["type"] = (*this)(component.type(), ns);
    }
  }
  else
    result["name"]=json_stringt("unknown");

  return result;
}

std::string json_exprt::from_constant(
  const namespacet &ns,
  const constant_exprt &expr)
{
  return format_constantt()(expr);
}

std::string json_exprt::from_type(const namespacet &ns, const typet &type)
{
  std::stringstream ss;
  ss << format(ns.follow(type));
  return ss.str();
}

/// Output a CBMC expression in json.
/// \param expr: an expression
/// \param ns: a namespace
/// \return a json object
json_objectt json_exprt::operator()(
  const exprt &expr,
  const namespacet &ns)
{
  json_objectt result;

  const typet &type=ns.follow(expr.type());

  if(expr.id()==ID_constant)
  {
    const typet &underlying_type=
      type.id()==ID_c_bit_field?type.subtype():
      type;

    std::string type_string = from_type(ns, underlying_type);
    const constant_exprt &constant_expr=to_constant_expr(expr);
    std::string value_string = from_constant(ns, constant_expr);

    if(type.id()==ID_unsignedbv ||
       type.id()==ID_signedbv ||
       type.id()==ID_c_bit_field)
    {
      std::size_t width=to_bitvector_type(type).get_width();

      result["name"]=json_stringt("integer");
      result["binary"]=json_stringt(id2string(constant_expr.get_value()));
      result["width"]=json_numbert(std::to_string(width));
      result["type"]=json_stringt(type_string);
      result["data"]=json_stringt(value_string);
    }
    else if(type.id()==ID_c_enum)
    {
      result["name"]=json_stringt("integer");
      result["binary"]=json_stringt(id2string(constant_expr.get_value()));
      result["width"]=json_numbert(type.subtype().get_string(ID_width));
      result["type"]=json_stringt("enum");
      result["data"]=json_stringt(value_string);
    }
    else if(type.id()==ID_c_enum_tag)
    {
      constant_exprt tmp;
      tmp.type()=ns.follow_tag(to_c_enum_tag_type(type));
      tmp.set_value(to_constant_expr(expr).get_value());
      result = (*this)(tmp, ns);
    }
    else if(type.id()==ID_bv)
    {
      result["name"]=json_stringt("bitvector");
      result["binary"]=json_stringt(id2string(constant_expr.get_value()));
    }
    else if(type.id()==ID_fixedbv)
    {
      result["name"]=json_stringt("fixed");
      result["width"]=json_numbert(type.get_string(ID_width));
      result["binary"]=json_stringt(id2string(constant_expr.get_value()));
      result["data"]=
        json_stringt(fixedbvt(to_constant_expr(expr)).to_ansi_c_string());
    }
    else if(type.id()==ID_floatbv)
    {
      result["name"]=json_stringt("float");
      result["width"]=json_numbert(type.get_string(ID_width));
      result["binary"]=json_stringt(id2string(constant_expr.get_value()));
      result["data"]=
        json_stringt(ieee_floatt(to_constant_expr(expr)).to_ansi_c_string());
    }
    else if(type.id()==ID_pointer)
    {
      result["name"]=json_stringt("pointer");
      result["type"]=json_stringt(type_string);
      exprt simpl_expr=simplify_json_expr(expr, ns);
      if(simpl_expr.get(ID_value)==ID_NULL ||
         // remove typecast on NULL
         (simpl_expr.id()==ID_constant && simpl_expr.type().id()==ID_pointer &&
          simpl_expr.op0().get(ID_value)==ID_NULL))
        result["data"]=json_stringt(value_string);
      else if(simpl_expr.id()==ID_symbol)
      {
        const irep_idt &ptr_id=to_symbol_expr(simpl_expr).get_identifier();
        identifiert identifier(id2string(ptr_id));
        DATA_INVARIANT(
          !identifier.components.empty(),
          "pointer identifier should have non-empty components");
        result["data"]=json_stringt(identifier.components.back());
      }
    }
    else if(type.id()==ID_bool)
    {
      result["name"]=json_stringt("boolean");
      result["binary"]=json_stringt(expr.is_true()?"1":"0");
      result["data"]=jsont::json_boolean(expr.is_true());
    }
    else if(type.id()==ID_c_bool)
    {
      result["name"]=json_stringt("integer");
      result["width"]=json_numbert(type.get_string(ID_width));
      result["type"]=json_stringt(type_string);
      result["binary"]=json_stringt(expr.get_string(ID_value));
      result["data"]=json_stringt(value_string);
    }
    else if(type.id()==ID_string)
    {
      result["name"]=json_stringt("string");
      result["data"]=json_stringt(id2string(constant_expr.get_value()));
    }
    else
    {
      result["name"]=json_stringt("unknown");
    }
  }
  else if(expr.id()==ID_array)
  {
    result["name"]=json_stringt("array");
    json_arrayt &elements=result["elements"].make_array();

    std::size_t index=0;

    forall_operands(it, expr)
    {
      json_objectt &e=elements.push_back().make_object();
      e["index"]=json_numbert(std::to_string(index));
      e["value"] = (*this)(*it, ns);
      index++;
    }
  }
  else if(expr.id()==ID_struct)
  {
    result["name"]=json_stringt("struct");

    // these are expected to have a struct type
    if(type.id()==ID_struct)
    {
      const struct_typet &struct_type=to_struct_type(type);
      const struct_typet::componentst &components=struct_type.components();
      DATA_INVARIANT(
        components.size()==expr.operands().size(),
        "number of struct components should match with its type");

      json_arrayt &members=result["members"].make_array();
      for(std::size_t m=0; m<expr.operands().size(); m++)
      {
        json_objectt &e=members.push_back().make_object();
        e["value"] = (*this)(expr.operands()[m], ns);
        e["name"]=json_stringt(id2string(components[m].get_name()));
      }
    }
  }
  else if(expr.id()==ID_union)
  {
    result["name"]=json_stringt("union");

    const union_exprt &union_expr=to_union_expr(expr);
    json_objectt &e=result["member"].make_object();
    e["value"] = (*this)(union_expr.op(), ns);
    e["name"]=json_stringt(id2string(union_expr.get_component_name()));
  }
  else
    result["name"]=json_stringt("unknown");

  return result;
}
