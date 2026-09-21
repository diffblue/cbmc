/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include "cpp_typecheck.h"

#include <functional>

void cpp_typecheckt::do_virtual_table(const symbolt &symbol)
{
  PRECONDITION(symbol.type.id() == ID_struct);

  // builds virtual-table value maps: (class x virtual_name x value)
  std::map<irep_idt, std::map<irep_idt, exprt> > vt_value_maps;

  const struct_typet &struct_type=to_struct_type(symbol.type);

  for(std::size_t i=0; i < struct_type.components().size(); i++)
  {
    const struct_typet::componentt &compo=struct_type.components()[i];
    if(!compo.get_bool(ID_is_virtual))
      continue;

    const code_typet &code_type=to_code_type(compo.type());
    DATA_INVARIANT(code_type.parameters().size() > 0, "parameters expected");

    const pointer_typet &parameter_pointer_type=
      to_pointer_type(code_type.parameters()[0].type());

    const irep_idt &class_id =
      parameter_pointer_type.base_type().get(ID_identifier);

    std::map<irep_idt, exprt> &value_map =
      vt_value_maps[class_id];

    exprt e=symbol_exprt(compo.get_name(), code_type);

    if(compo.get_bool(ID_is_pure_virtual))
    {
      pointer_typet code_pointer_type=pointer_type(code_type);
      e=null_pointer_exprt(code_pointer_type);
      value_map[compo.get(ID_virtual_name)] = e;
    }
    else
    {
      address_of_exprt address(e);
      value_map[compo.get(ID_virtual_name)] = address;
    }
  }

  // The value of the vtable struct `vt_name' for a complete object of
  // `symbol': the entries of its class, and -- as the first member `@base' --
  // the value of the primary base's vtable struct it embeds (Itanium C++ ABI
  // 2.4: the primary base's entries come first in the shared vtable).
  // Returns nil when a slot's value does not fit its component (an earlier
  // front-end error left the class partially elaborated).
  std::function<exprt(const irep_idt &)> vtable_value =
    [&](const irep_idt &vt_name) -> exprt
  {
    const symbolt &vt_symb_type = lookup(vt_name);
    const struct_typet &vt_type = to_struct_type(vt_symb_type.type);
    const std::string prefix = "virtual_table::";
    const irep_idt class_id = id2string(vt_name).substr(prefix.size());
    const auto map_it = vt_value_maps.find(class_id);

    struct_exprt values({}, struct_tag_typet(vt_name));

    for(const auto &compo : vt_type.components())
    {
      if(compo.get_is_padding())
      {
        // a padding component of the vtable's layout: zero
        values.operands().push_back(from_integer(0, compo.type()));
        continue;
      }
      if(compo.get_base_name() == "@base")
      {
        exprt base_value =
          vtable_value(to_struct_tag_type(compo.type()).get_identifier());
        if(base_value.is_nil())
          return nil_exprt{};
        values.operands().push_back(std::move(base_value));
        continue;
      }
      if(map_it == vt_value_maps.end())
        return nil_exprt{};
      const auto cit2 = map_it->second.find(compo.get_base_name());
      CHECK_RETURN(cit2 != map_it->second.end());
      const exprt &value = cit2->second;
      if(value.type() != compo.type())
        return nil_exprt{};
      values.operands().push_back(value);
    }

    return std::move(values);
  };

  // create virtual-table symbol variables
  for(std::map<irep_idt, std::map<irep_idt, exprt> >::const_iterator cit =
      vt_value_maps.begin(); cit!=vt_value_maps.end(); cit++)
  {
    const symbolt &late_cast_symb = lookup(cit->first);
    const symbolt &vt_symb_type =
      lookup("virtual_table::" + id2string(late_cast_symb.name));

    symbolt vt_symb_var{
      id2string(vt_symb_type.name) + "@" + id2string(symbol.name),
      struct_tag_typet(vt_symb_type.name),
      symbol.mode};
    vt_symb_var.base_name=
      id2string(vt_symb_type.base_name) + "@" + id2string(symbol.base_name);
    vt_symb_var.module=module;
    vt_symb_var.location=vt_symb_type.location;
    vt_symb_var.is_lvalue=true;
    vt_symb_var.is_static_lifetime=true;

    // do the values
    exprt values = vtable_value(vt_symb_type.name);
    if(values.is_nil())
    {
      // Type mismatch between a vtable slot's component and the
      // function value inserted there.  This can occur when an
      // earlier front-end error (e.g., a failed implicit
      // conversion in a base-class constructor invocation) left
      // the class partially elaborated.  Skip vtable
      // construction rather than aborting via DATA_INVARIANT.
      continue;
    }
    vt_symb_var.value = std::move(values);

    bool failed = !symbol_table.insert(std::move(vt_symb_var)).second;
    CHECK_RETURN(!failed);
  }
}

irep_idt cpp_typecheckt::primary_base(const irep_idt &class_id) const
{
  const symbolt *sym = symbol_table.lookup(class_id);
  if(sym == nullptr || sym->type.id() != ID_struct)
    return irep_idt{};

  // Itanium C++ ABI 2.4 II.1: the first non-virtual dynamic base class in
  // declaration order
  for(const auto &base : to_struct_type(sym->type).bases())
  {
    if(base.get_bool(ID_virtual) || base.type().id() != ID_struct_tag)
      continue;
    const irep_idt base_id = to_struct_tag_type(base.type()).get_identifier();
    if(!vtable_pointer_component(base_id).empty())
      return base_id;
  }

  return irep_idt{};
}

irep_idt
cpp_typecheckt::vtable_pointer_component(const irep_idt &class_id) const
{
  const symbolt *sym = symbol_table.lookup(class_id);
  if(sym == nullptr || sym->type.id() != ID_struct)
    return irep_idt{};

  const irep_idt own = id2string(class_id) + "::@vtable_pointer";
  for(const auto &c : to_struct_type(sym->type).components())
    if(c.get_bool(ID_is_vtptr) && c.get_name() == own)
      return own;

  const irep_idt pb = primary_base(class_id);
  if(pb.empty())
    return irep_idt{};

  return vtable_pointer_component(pb);
}

std::vector<irep_idt>
cpp_typecheckt::vtable_chain(const irep_idt &class_id) const
{
  std::vector<irep_idt> chain;
  for(irep_idt c = class_id; !c.empty(); c = primary_base(c))
  {
    const irep_idt vt_name = "virtual_table::" + id2string(c);
    if(symbol_table.has_symbol(vt_name))
      chain.push_back(vt_name);
  }
  return chain;
}

exprt cpp_typecheckt::vtable_pointer_value(
  const symbolt &most_derived,
  const struct_typet::componentt &vtptr) const
{
  const typet &vt_tag = to_pointer_type(vtptr.type()).base_type();
  if(vt_tag.id() != ID_struct_tag)
    return nil_exprt{};
  const irep_idt target_vt = to_struct_tag_type(vt_tag).get_identifier();

  // every class of the hierarchy: the class itself and its (transitive) bases
  std::vector<irep_idt> classes;
  std::set<irep_idt> seen;
  std::vector<irep_idt> work{most_derived.name};
  while(!work.empty())
  {
    const irep_idt c = work.back();
    work.pop_back();
    if(!seen.insert(c).second)
      continue;
    classes.push_back(c);
    const symbolt *sym = symbol_table.lookup(c);
    if(sym == nullptr || sym->type.id() != ID_struct)
      continue;
    for(const auto &base : to_struct_type(sym->type).bases())
      if(base.type().id() == ID_struct_tag)
        work.push_back(to_struct_tag_type(base.type()).get_identifier());
  }

  // the class whose vtable chain reaches the pointer's vtable struct through
  // the most embedding levels is the most derived one sharing the pointer
  std::vector<irep_idt> best_chain;
  std::size_t best_depth = 0;
  bool found = false;
  for(const auto &c : classes)
  {
    const std::vector<irep_idt> chain = vtable_chain(c);
    for(std::size_t depth = 0; depth < chain.size(); ++depth)
    {
      if(chain[depth] == target_vt && (!found || depth > best_depth))
      {
        found = true;
        best_depth = depth;
        best_chain = chain;
      }
    }
  }
  if(!found)
    return nil_exprt{};

  const symbolt *vt_object = symbol_table.lookup(
    id2string(best_chain.front()) + "@" + id2string(most_derived.name));
  if(vt_object == nullptr)
    return nil_exprt{};

  // descend into the embedded `@base' members down to the target struct
  exprt value = vt_object->symbol_expr();
  for(std::size_t depth = 1; depth <= best_depth; ++depth)
  {
    value = member_exprt(
      value,
      id2string(best_chain[depth - 1]) + "::@base",
      struct_tag_typet(best_chain[depth]));
  }

  return address_of_exprt(value, to_pointer_type(vtptr.type()));
}
