/*******************************************************************\

Module: Remove gcc's 'variable-length array members'

Author: Daniel Kroening

Date:   February 2019

\*******************************************************************/

/// \file
/// Remove gcc's 'variable-length array members'
/// https://gcc.gnu.org/onlinedocs/gcc/Variable-Length.html

#include "remove_variable_length_array_member.h"

#include "goto_model.h"

#include <util/c_types.h>
#include <util/pointer_offset_size.h>

bool has_variable_length_array_member(const typet &type, const namespacet &ns)
{
  if(type.id() == ID_struct_tag)
  {
    const auto &struct_type = ns.follow_tag(to_struct_tag_type(type));

    for(auto &c : struct_type.components())
    {
      const auto &c_type = c.type();
      if(c_type.id() == ID_struct_tag)
      {
        if(has_variable_length_array_member(c.type(), ns))
          return true;
      }
      else if(c_type.id() == ID_array)
      {
        if(!to_array_type(c_type).size().is_constant())
          return true;
      }
    }

    return false;
  }
  else
    return false;
}

static array_typet replacement_type(const typet &type, const namespacet &ns)
{
  const auto size = size_of_expr(type, ns);
  CHECK_RETURN(size.has_value());
  return array_typet(char_type(), size.value());
}

static optionalt<exprt>
adjust(exprt src, const std::map<irep_idt, typet> &new_types)
{
  if(src.id() == ID_symbol)
  {
    const auto identifier = to_symbol_expr(src).get_identifier();
    auto t_it = new_types.find(identifier);
    if(t_it == new_types.end())
      return src;
    else
      return symbol_exprt(identifier, t_it->second);
  }
  else
  {
    bool adjustment_needed = false;
    exprt old_src = src;

    for(auto &op : src.operands)
    {
      auto op_adjusted = adjust(op, new_types);
      if(op_adjusted.has_value())
      {
        adjustment_needed = true;
        op = op_adjusted.value();
      }
    }

    if(adjustment_needed)
    {
      if(src.id() == ID_member)
      {
        auto &member_expr = to_member_expr(src);
        if(member_expr.compound_op().type().id() == ID_array)
        {
          // the struct or union got turned into an array
        }
      }

      return src;
    }
    else
      return {};
  }
}

void remove_variable_length_array_member(
  goto_functiont &f,
  const namespacet &ns)
{
  // gather symbols that need to be adjusted
  std::map<irep_idt, typet> new_types;

  for(const auto &i : f.body.instructions)
  {
    if(i.is_decl())
    {
      if(has_variable_length_array_member(i.get_decl().symbol().type(), ns))
      {
        auto decl = i.get_decl();
        auto new_type = replacement_type(decl.symbol().type(), ns);
        new_types[decl.symbol().get_identifier()] = new_type;
      }
    }
  }

  // now adjust all expressions
  f.body.transform([&new_types](exprt src) { return adjust(src, new_types); });
}

/// removes gcc's 'variable-length array members'
void remove_variable_length_array_member(goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  for(auto &f : goto_model.goto_functions.function_map)
    remove_variable_length_array_member(f.second, ns);
}
