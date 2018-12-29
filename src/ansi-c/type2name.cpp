/*******************************************************************\

Module: Type Naming for C

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// Type Naming for C

#include "type2name.h"

#include <util/arith_tools.h>
#include <util/invariant.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

typedef std::unordered_map<irep_idt, std::pair<size_t, bool>> symbol_numbert;

static std::string type2name(
  const typet &type,
  const namespacet &ns,
  symbol_numbert &symbol_number);

static std::string type2name_symbol(
  const typet &type,
  const namespacet &ns,
  symbol_numbert &symbol_number)
{
  const irep_idt &identifier=type.get(ID_identifier);

  const symbolt *symbol;

  if(ns.lookup(identifier, symbol))
    return "SYM#"+id2string(identifier)+"#";

  assert(symbol && symbol->is_type);

  if(symbol->type.id()!=ID_struct &&
     symbol->type.id()!=ID_union)
    return type2name(symbol->type, ns, symbol_number);

  std::string result;

  // assign each symbol a number when seen for the first time
  std::pair<symbol_numbert::iterator, bool> entry=
    symbol_number.insert(std::make_pair(
        identifier,
        std::make_pair(symbol_number.size(), true)));

  // new entry, add definition
  if(entry.second)
  {
    result="SYM#"+std::to_string(entry.first->second.first);
    result+="={";
    result+=type2name(symbol->type, ns, symbol_number);
    result+='}';

    entry.first->second.second=false;
  }
#if 0
  // in recursion, print the shorthand only
  else if(entry.first->second.second)
    result="SYM#"+std::to_string(entry.first->second.first);
  // entering recursion
  else
  {
    entry.first->second.second=true;
    result=type2name(symbol->type, ns, symbol_number);
    entry.first->second.second=false;
  }
#else
  // shorthand only as structs/unions are always symbols
  else
    result="SYM#"+std::to_string(entry.first->second.first);
#endif

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

static bool parent_is_sym_check=false;
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
    type.id() == ID_symbol_type || type.id() == ID_c_enum_tag ||
    type.id() == ID_struct_tag || type.id() == ID_union_tag)
  {
    parent_is_sym_check=true;
    result+=type2name_symbol(type, ns, symbol_number);
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union)
  {
    assert(parent_is_sym_check);
    parent_is_sym_check=false;
    if(type.id()==ID_struct)
      result+="ST";
    if(type.id()==ID_union)
      result+="UN";
    result+='[';
    bool first = true;
    for(const auto &c : to_struct_union_type(type).components())
    {
      if(!first)
        result+='|';
      else
        first = false;

      result += type2name(c.type(), ns, symbol_number);
      const irep_idt &component_name = c.get_name();
      CHECK_RETURN(!component_name.empty());
      result+="'"+id2string(component_name)+"'";
    }
    result+=']';
  }
  else if(type.id()==ID_incomplete_struct)
    result +="ST?";
  else if(type.id()==ID_incomplete_union)
    result +="UN?";
  else if(type.id()==ID_c_enum)
  {
    result +="EN";
    const c_enum_typet &t=to_c_enum_type(type);
    const c_enum_typet::memberst &members=t.members();
    result+='[';
    for(c_enum_typet::memberst::const_iterator
        it=members.begin();
        it!=members.end();
        ++it)
    {
      if(it!=members.begin())
        result+='|';
      result+=id2string(it->get_value());
      result+="'"+id2string(it->get_identifier())+"'";
    }
  }
  else if(type.id()==ID_incomplete_c_enum)
    result +="EN?";
  else if(type.id()==ID_c_bit_field)
    result+="BF"+pointer_offset_bits_as_string(type, ns);
  else if(type.id()==ID_vector)
    result+="VEC"+type.get_string(ID_size);
  else
    throw "unknown type '"+type.id_string()+"' encountered";

  if(type.has_subtype())
  {
    result+='{';
    result+=type2name(type.subtype(), ns, symbol_number);
    result+='}';
  }

  if(type.has_subtypes())
  {
    result+='$';
    forall_subtypes(it, type)
    {
      result+=type2name(*it, ns, symbol_number);
      result+='|';
    }
    result[result.size()-1]='$';
  }

  return result;
}

std::string type2name(const typet &type, const namespacet &ns)
{
  parent_is_sym_check=true;
  symbol_numbert symbol_number;
  return type2name(type, ns, symbol_number);
}
