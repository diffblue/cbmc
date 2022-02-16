/*******************************************************************\

Module: Type Naming for C

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// Type Naming for C

#include "type2name.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/invariant.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <regex>

typedef std::unordered_map<irep_idt, std::pair<size_t, bool>> symbol_numbert;

static std::string type2name(
  const typet &type,
  const namespacet &ns,
  symbol_numbert &symbol_number);

static std::string type2name_tag(
  const tag_typet &type,
  const namespacet &ns,
  symbol_numbert &symbol_number)
{
  const irep_idt &identifier = type.get_identifier();

  const symbolt *symbol;

  if(ns.lookup(identifier, symbol))
    return "SYM#"+id2string(identifier)+"#";

  assert(symbol && symbol->is_type);

  if(symbol->type.id()!=ID_struct &&
     symbol->type.id()!=ID_union)
    return type2name(symbol->type, ns, symbol_number);

  // assign each symbol a number when seen for the first time
  std::pair<symbol_numbert::iterator, bool> entry=
    symbol_number.insert(std::make_pair(
        identifier,
        std::make_pair(symbol_number.size(), true)));

  std::string result = "SYM" +
                       id2string(to_struct_union_type(symbol->type).get_tag()) +
                       '#' + std::to_string(entry.first->second.first);

  // new entry, add definition
  if(entry.second)
  {
    result+="={";
    result+=type2name(symbol->type, ns, symbol_number);
    result+='}';

    entry.first->second.second=false;
  }

  return result;
}

static std::string pointer_offset_bits_as_string(
  const typet &type,
  const namespacet &ns)
{
  auto bits = pointer_offset_bits(type, ns);
  CHECK_RETURN(bits.has_value());
  return integer2string(*bits);
}

static std::string type2name(
  const typet &type,
  const namespacet &ns,
  symbol_numbert &symbol_number)
{
  std::string result;

  // qualifiers first
  if(type.get_bool(ID_C_constant))
    result+='c';

  if(type.get_bool(ID_C_restricted))
    result+='r';

  if(type.get_bool(ID_C_volatile))
    result+='v';

  if(type.get_bool(ID_C_transparent_union))
    result+='t';

  if(type.get_bool(ID_C_noreturn))
    result+='n';

  // this isn't really a qualifier, but the linker needs to
  // distinguish these - should likely be fixed in the linker instead
  if(!type.source_location().get_function().empty())
    result+='l';

  if(type.id().empty())
    throw "empty type encountered";
  else if(type.id()==ID_empty)
    result+='V';
  else if(type.id()==ID_signedbv)
    result+="S" + pointer_offset_bits_as_string(type, ns);
  else if(type.id()==ID_unsignedbv)
    result+="U" + pointer_offset_bits_as_string(type, ns);
  else if(type.id()==ID_bool ||
          type.id()==ID_c_bool)
    result+='B';
  else if(type.id()==ID_integer)
    result+='I';
  else if(type.id()==ID_real)
    result+='R';
  else if(type.id()==ID_complex)
    result+='C';
  else if(type.id()==ID_floatbv)
    result+="F" + pointer_offset_bits_as_string(type, ns);
  else if(type.id()==ID_fixedbv)
    result+="X" + pointer_offset_bits_as_string(type, ns);
  else if(type.id()==ID_natural)
    result+='N';
  else if(type.id()==ID_pointer)
  {
    if(type.get_bool(ID_C_reference))
      result+='&';
    else
      result+='*';
  }
  else if(type.id()==ID_code)
  {
    const code_typet &t=to_code_type(type);
    const code_typet::parameterst parameters=t.parameters();
    result+=type2name(t.return_type(), ns, symbol_number)+"(";

    for(code_typet::parameterst::const_iterator
        it=parameters.begin();
        it!=parameters.end();
        it++)
    {
      if(it!=parameters.begin())
        result+='|';
      result+=type2name(it->type(), ns, symbol_number);
    }

    if(t.has_ellipsis())
    {
      if(!parameters.empty())
        result+='|';
      result+="...";
    }

    result+=")->";
    result+=type2name(t.return_type(), ns, symbol_number);
  }
  else if(type.id()==ID_array)
  {
    const exprt &size = to_array_type(type).size();

    if(size.id() == ID_symbol)
      result += "ARR" + id2string(to_symbol_expr(size).get_identifier());
    else
    {
      const auto size_int = numeric_cast<mp_integer>(size);

      if(!size_int.has_value())
        result += "ARR?";
      else
        result += "ARR" + integer2string(*size_int);
    }
  }
  else if(
    type.id() == ID_c_enum_tag || type.id() == ID_struct_tag ||
    type.id() == ID_union_tag)
  {
    result += type2name_tag(to_tag_type(type), ns, symbol_number);
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union)
  {
    const auto &struct_union_type = to_struct_union_type(type);

    if(struct_union_type.is_incomplete())
    {
      if(type.id() == ID_struct)
        result += "ST?";
      else if(type.id() == ID_union)
        result += "UN?";
    }
    else
    {
      if(type.id() == ID_struct)
        result += "ST";
      if(type.id() == ID_union)
        result += "UN";
      result += '[';
      bool first = true;
      for(const auto &c : struct_union_type.components())
      {
        if(!first)
          result += '|';
        else
          first = false;

        result += type2name(c.type(), ns, symbol_number);
        const irep_idt &component_name = c.get_name();
        CHECK_RETURN(!component_name.empty());
        result += "'" + id2string(component_name) + "'";
      }
      result += ']';
    }
  }
  else if(type.id()==ID_c_enum)
  {
    const c_enum_typet &t=to_c_enum_type(type);

    if(t.is_incomplete())
      result += "EN?";
    else
    {
      result += "EN";
      const c_enum_typet::memberst &members = t.members();
      result += '[';
      for(c_enum_typet::memberst::const_iterator it = members.begin();
          it != members.end();
          ++it)
      {
        if(it != members.begin())
          result += '|';
        result += id2string(it->get_value());
        result += "'" + id2string(it->get_identifier()) + "'";
      }
    }
  }
  else if(type.id()==ID_c_bit_field)
    result+="BF"+pointer_offset_bits_as_string(type, ns);
  else if(type.id()==ID_vector)
    result+="VEC"+type.get_string(ID_size);
  else
    throw "unknown type '"+type.id_string()+"' encountered";

  if(type.has_subtype())
  {
    result+='{';
    result +=
      type2name(to_type_with_subtype(type).subtype(), ns, symbol_number);
    result+='}';
  }

  if(type.has_subtypes())
  {
    result+='$';
    for(const typet &subtype : to_type_with_subtypes(type).subtypes())
    {
      result += type2name(subtype, ns, symbol_number);
      result+='|';
    }
    result[result.size()-1]='$';
  }

  return result;
}

std::string type2name(const typet &type, const namespacet &ns)
{
  symbol_numbert symbol_number;
  return type2name(type, ns, symbol_number);
}

/// type2name generates strings that aren't valid C identifiers
/// If we want utilities like dump_c to work properly identifiers
/// should ideally always be valid C identifiers
/// This replaces some invalid characters that can appear in type2name output.
std::string type_name2type_identifier(const std::string &name)
{
  const auto replace_special_characters = [](const std::string &name) {
    std::string result{};
    for(char c : name)
    {
      switch(c)
      {
      case '*':
        result += "_ptr_";
        break;
      case '{':
        result += "_start_sub_";
        break;
      case '}':
        result += "_end_sub_";
        break;
      default:
        result += c;
        break;
      }
    }
    return result;
  };
  const auto replace_invalid_characters_with_underscore =
    [](const std::string &identifier) {
      static const std::regex non_alpha_numeric{"[^A-Za-z0-9\x80-\xff]+"};
      return std::regex_replace(identifier, non_alpha_numeric, "_");
    };
  const auto strip_leading_digits = [](const std::string &identifier) {
    static const std::regex identifier_regex{
      "[A-Za-z\x80-\xff_][A-Za-z0-9_\x80-\xff]*"};
    std::smatch match_results;
    bool found = std::regex_search(identifier, match_results, identifier_regex);
    POSTCONDITION(found);
    return match_results.str(0);
  };
  return strip_leading_digits(replace_invalid_characters_with_underscore(
    replace_special_characters(name)));
}

std::string type_to_partial_identifier(const typet &type, const namespacet &ns)
{
  return type_name2type_identifier(type2name(type, ns));
}
