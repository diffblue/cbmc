/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include "cpp_typecheck.h"

#include <functional>

void cpp_typecheckt::build_virtual_thunk_body(
  symbolt &thunk,
  const irep_idt &target,
  const typet &target_type,
  const irep_idt &base_class,
  const struct_typet &derived)
{
  const code_typet &code_type = to_code_type(thunk.type);
  const code_typet::parameterst &args = code_type.parameters();
  PRECONDITION(!args.empty());

  exprt this_expr = lookup(args[0].get_identifier()).symbol_expr();
  const typet &this_target_type =
    to_code_type(target_type).parameters()[0].type();

  // A base subobject that shares the derived class's virtual pointer (the
  // primary-base chain, Itanium C++ ABI 2.4 II.1) is at offset 0 and needs
  // no adjustment; any other dynamic base subobject starts at the offset of
  // its own virtual pointer in the derived class's layout.
  const irep_idt base_vtptr = vtable_pointer_component(base_class);
  const bool is_primary_base =
    !base_vtptr.empty() &&
    base_vtptr == vtable_pointer_component(derived.get(ID_name));

  exprt late_cast;
  std::optional<mp_integer> base_off;
  if(!is_primary_base && !base_vtptr.empty())
    base_off = member_offset(derived, base_vtptr, *this);
  if(base_off.has_value() && *base_off > 0)
  {
    auto char_ptr =
      typecast_exprt(this_expr, pointer_type(unsigned_char_type()));
    auto adjusted =
      minus_exprt(char_ptr, from_integer(*base_off, pointer_diff_type()));
    late_cast = typecast_exprt(adjusted, this_target_type);
  }
  else
    late_cast = typecast_exprt(this_expr, this_target_type);

  // the call must be direct (non-virtual): it would otherwise dispatch back
  // through the vtable
  typet direct_type = target_type;
  direct_type.remove(ID_C_is_virtual);

  side_effect_expr_function_callt expr_call(
    symbol_exprt(target, direct_type),
    {late_cast},
    uninitialized_typet{},
    source_locationt{});
  expr_call.arguments().reserve(args.size());

  // the first parameter (this) was added as late_cast above
  for(std::size_t j = 1; j < args.size(); ++j)
    expr_call.arguments().push_back(
      lookup(args[j].get_identifier()).symbol_expr());

  if(
    code_type.return_type().id() != ID_empty &&
    code_type.return_type().id() != ID_destructor)
  {
    expr_call.type() = to_code_type(target_type).return_type();
    thunk.value = code_blockt{{code_frontend_returnt(std::move(expr_call))}};
  }
  else
  {
    thunk.value = code_blockt{{code_expressiont(std::move(expr_call))}};
  }
}

void cpp_typecheckt::finalize_virtual_thunks(const symbolt &symbol)
{
  PRECONDITION(symbol.type.id() == ID_struct);

  for(const auto &compo : to_struct_type(symbol.type).components())
  {
    if(compo.type().id() != ID_code || compo.get_bool(ID_from_base))
      continue;
    const irep_idt target = compo.type().get("#thunk_target");
    if(target.empty())
      continue;
    symbolt *thunk = symbol_table.get_writeable(compo.get_name());
    const symbolt *target_symbol = symbol_table.lookup(target);
    if(thunk == nullptr || target_symbol == nullptr)
      continue;
    build_virtual_thunk_body(
      *thunk,
      target,
      target_symbol->type,
      compo.type().get("#thunk_base"),
      to_struct_type(symbol.type));
  }
}

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
