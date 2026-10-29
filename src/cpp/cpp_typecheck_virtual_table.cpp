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

#include <algorithm>
#include <functional>
#include <map>
#include <set>

/// Whether \p vtptr is the virtual pointer of a base class subobject, in the
/// non-virtual part, of a class occurring more than once in the lattice:
/// add_base_components renames every such occurrence but the first
/// (`name@/\<path\>').
static bool
is_repeated_subobject_vtable_pointer(const struct_typet::componentt &vtptr)
{
  return vtptr.get(ID_C_virtual_base).empty() &&
         id2string(vtptr.get_name()).find("@/") != std::string::npos;
}

void cpp_typecheckt::build_virtual_thunk_body(
  symbolt &thunk,
  const irep_idt &target,
  const typet &target_type,
  const irep_idt &base_class,
  const struct_typet &derived)
{
  // A base subobject that shares the derived class's virtual pointer (the
  // primary-base chain, Itanium C++ ABI 2.4 II.1) is at offset 0 and needs
  // no adjustment; any other dynamic base subobject starts at the offset of
  // its own virtual pointer in the derived class's layout.
  const irep_idt base_vtptr = vtable_pointer_component(base_class);
  const bool is_primary_base =
    !base_vtptr.empty() &&
    base_vtptr == vtable_pointer_component(derived.get(ID_name));
  std::optional<mp_integer> base_off;
  if(!is_primary_base && !base_vtptr.empty())
    base_off = member_offset(derived, base_vtptr, *this);
  build_this_adjusting_thunk_body(thunk, target, target_type, base_off);
}

void cpp_typecheckt::build_this_adjusting_thunk_body(
  symbolt &thunk,
  const irep_idt &target,
  const typet &target_type,
  const std::optional<mp_integer> &base_off)
{
  const code_typet &code_type = to_code_type(thunk.type);
  const code_typet::parameterst &args = code_type.parameters();
  PRECONDITION(!args.empty());

  exprt this_expr = lookup(args[0].get_identifier()).symbol_expr();
  const typet &this_target_type =
    to_code_type(target_type).parameters()[0].type();

  exprt late_cast;
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

  // the first parameter (this) was added as late_cast above.  The thunk
  // forwards its arguments to the final overrider ([class.virtual]/14) with
  // the same parameter types.  A named rvalue reference parameter is an
  // lvalue ([expr.prim.id.unqual]/3), which cannot bind to the overrider's
  // rvalue reference parameter; it is passed on as an xvalue (inside a
  // system header, where conversion failures drop the body, the thunk was
  // dropped and the virtual call returned a nondeterministic value).
  for(std::size_t j = 1; j < args.size(); ++j)
  {
    exprt argument = lookup(args[j].get_identifier()).symbol_expr();
    // `static_cast<T &&>(a)' for a parameter `T &&a' ([expr.static.cast]/3:
    // an xvalue)
    if(is_rvalue_reference(argument.type()))
      argument = typecast_exprt{argument, argument.type()};
    expr_call.arguments().push_back(std::move(argument));
  }

  // the target's hidden `@most_derived' parameter, which the thunk (of the
  // base's signature) lacks: a virtual call reaches the complete object's
  // destructor
  const code_typet::parameterst &target_parameters =
    to_code_type(target_type).parameters();
  if(
    target_parameters.size() == args.size() + 1 &&
    target_parameters.back().get_base_name() == "@most_derived")
  {
    expr_call.arguments().push_back(true_exprt());
  }

  if(
    code_type.return_type().id() != ID_empty &&
    code_type.return_type().id() != ID_destructor)
  {
    const typet &target_return = to_code_type(target_type).return_type();
    expr_call.type() = target_return;
    const typet &thunk_return = code_type.return_type();
    if(
      thunk_return != target_return && thunk_return.id() == ID_pointer &&
      target_return.id() == ID_pointer &&
      to_pointer_type(thunk_return).base_type().id() == ID_struct_tag &&
      to_pointer_type(target_return).base_type().id() == ID_struct_tag)
    {
      // N5008 [class.virtual]/9: a covariant overrider's result converted to
      // the overridden function's return type -- derived-to-base
      // ([conv.ptr]/3; [dcl.init.ref]/5 for a reference), a null pointer
      // staying null
      if(is_reference(thunk_return) || is_rvalue_reference(thunk_return))
      {
        exprt converted = std::move(expr_call);
        make_ptr_typecast(converted, to_pointer_type(thunk_return));
        thunk.value = code_blockt{{code_frontend_returnt(converted)}};
      }
      else
      {
        const irep_idt result_id = id2string(thunk.name) + "::$result";
        if(!symbol_table.has_symbol(result_id))
        {
          symbolt result{result_id, target_return, thunk.mode};
          result.base_name = "$result";
          result.is_lvalue = true;
          result.is_file_local = true;
          result.is_thread_local = true;
          result.location = thunk.location;
          symbol_table.insert(std::move(result));
        }
        const symbol_exprt result_expr{result_id, target_return};
        exprt converted = result_expr;
        make_ptr_typecast(converted, to_pointer_type(thunk_return));
        code_blockt body;
        body.add(code_frontend_declt{result_expr});
        body.add(code_frontend_assignt{result_expr, std::move(expr_call)});
        body.add(code_frontend_returnt{if_exprt{
          equal_exprt{
            result_expr, null_pointer_exprt{to_pointer_type(target_return)}},
          null_pointer_exprt{to_pointer_type(thunk_return)},
          converted}});
        thunk.value = std::move(body);
      }
      return;
    }
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

void cpp_typecheckt::set_virtual_base_offsets(const symbolt &symbol)
{
  PRECONDITION(symbol.type.id() == ID_struct);
  const struct_typet &struct_type = to_struct_type(symbol.type);
  const namespacet ns(symbol_table);

  std::list<irep_idt> vbase_ids;
  get_virtual_bases(struct_type, vbase_ids);
  if(vbase_ids.empty())
    return;

  // where each virtual base starts in this complete object: its first
  // storage component (marked with the virtual base's identifier)
  std::map<irep_idt, mp_integer> vbase_offset;
  for(const auto &c : struct_type.components())
  {
    const irep_idt vb = c.get(ID_C_virtual_base);
    if(
      vb.empty() || vb == "$padding" || c.type().id() == ID_code ||
      c.get_bool(ID_is_type) || c.get_bool(ID_is_static))
    {
      continue;
    }
    const auto off = member_offset(struct_type, c.get_name(), ns);
    if(off.has_value() && vbase_offset.find(vb) == vbase_offset.end())
      vbase_offset[vb] = *off;
  }

  // every vtable object of this complete object, and the construction
  // tables of its direct bases with virtual bases (do_virtual_table)
  std::vector<std::pair<struct_typet::componentt, exprt>> pointers;
  for(const auto &c : struct_type.components())
    if(c.get_bool(ID_is_vtptr))
      pointers.emplace_back(c, vtable_pointer_value(symbol, c));
  for(const irep_idt &base_id : construction_vtable_bases(symbol.name))
    for(auto &install : construction_vtable_installs(symbol, base_id))
      pointers.push_back(std::move(install));

  for(const auto &pointer : pointers)
  {
    const struct_typet::componentt &c = pointer.first;
    const exprt &value = pointer.second;
    if(value.id() != ID_address_of)
      continue;
    // the vtable object, through the embedded `@base' members
    exprt object = to_address_of_expr(value).object();
    while(object.id() == ID_member)
      object = to_member_expr(object).compound();
    if(object.id() != ID_symbol)
      continue;
    // the subobject whose pointer this is starts where the pointer lies
    const auto subobject_offset = member_offset(struct_type, c.get_name(), ns);
    if(!subobject_offset.has_value())
      continue;

    // patch the offsets in the object's value, at every embedding level
    symbolt *vt_object =
      symbol_table.get_writeable(to_symbol_expr(object).get_identifier());
    if(vt_object == nullptr || vt_object->value.id() != ID_struct)
      continue;
    std::function<void(exprt &)> patch = [&](exprt &value)
    {
      if(value.type().id() != ID_struct_tag)
        return;
      const struct_typet &vt_type =
        ns.follow_tag(to_struct_tag_type(value.type()));
      const auto &comps = vt_type.components();
      auto &ops = value.operands();
      if(ops.size() != comps.size())
        return;
      for(std::size_t i = 0; i < comps.size(); ++i)
      {
        if(comps[i].get_base_name() == "@base")
        {
          patch(ops[i]);
          continue;
        }
        const irep_idt vb = comps[i].get(ID_C_virtual_base);
        if(vb.empty())
          continue;
        const auto vb_it = vbase_offset.find(vb);
        if(vb_it == vbase_offset.end())
          continue; // an empty virtual base: no storage to locate
        ops[i] =
          from_integer(vb_it->second - *subobject_offset, comps[i].type());
      }
    };
    patch(vt_object->value);
  }
}

void cpp_typecheckt::do_virtual_table(const symbolt &symbol)
{
  PRECONDITION(symbol.type.id() == ID_struct);

  // builds virtual-table value maps: (class x virtual_name x value)
  std::map<irep_idt, std::map<irep_idt, exprt> > vt_value_maps;

  const struct_typet &struct_type=to_struct_type(symbol.type);

  // The inherited entries first (a later non-virtual base's overrider of
  // an earlier base's function wins; those of a virtual base -- laid out
  // last, yet the least derived on its path -- never override), then the
  // class's own overriders and their thunks, which win over everything.
  for(int pass = 0; pass < 3; ++pass)
    for(std::size_t i = 0; i < struct_type.components().size(); i++)
    {
      const struct_typet::componentt &compo = struct_type.components()[i];
      if(!compo.get_bool(ID_is_virtual))
        continue;
      const bool from_virtual_base = !compo.get(ID_C_virtual_base).empty();
      if(pass == 0 && (!compo.get_bool(ID_from_base) || from_virtual_base))
        continue;
      if(pass == 1 && !from_virtual_base)
        continue;
      if(pass == 2 && compo.get_bool(ID_from_base))
        continue;

      const code_typet &code_type = to_code_type(compo.type());
      DATA_INVARIANT(code_type.parameters().size() > 0, "parameters expected");

      const pointer_typet &parameter_pointer_type =
        to_pointer_type(code_type.parameters()[0].type());

      const irep_idt &class_id =
        parameter_pointer_type.base_type().get(ID_identifier);

      // N5008 [class.mi]/4, [class.virtual]/2: when class_id occurs as more
      // than one base class subobject, the class's table for it serves its
      // FIRST occurrence (whose virtual pointer keeps its name, see
      // add_base_components); an overrider inherited through another path
      // belongs to another subobject (do_repeated_subobject_virtual_tables)
      if(pass == 0)
      {
        const auto &path = compo.find(ID_C_subobject_path).get_sub();
        if(!path.empty())
        {
          const auto subobjects = base_subobjects(struct_type, class_id);
          if(
            subobjects.size() > 1 && !subobjects.front().path.empty() &&
            path.front().id() != subobjects.front().path.front())
          {
            continue;
          }
        }
      }

      std::map<irep_idt, exprt> &value_map = vt_value_maps[class_id];

      if(
        pass == 1 &&
        value_map.find(compo.get(ID_virtual_name)) != value_map.end())
      {
        continue;
      }

      exprt e = symbol_exprt(compo.get_name(), code_type);

      if(compo.get_bool(ID_is_pure_virtual))
      {
        pointer_typet code_pointer_type = pointer_type(code_type);
        e = null_pointer_exprt(code_pointer_type);
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
      if(!compo.get(ID_C_virtual_base).empty())
      {
        // `@vbase_offset::<V>': filled in by set_virtual_base_offsets once
        // the class's layout (padding included) is final
        values.operands().push_back(from_integer(0, compo.type()));
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

  // create virtual-table symbol variables: one per class of the hierarchy
  // that has a vtable struct -- with virtual functions, or (Itanium C++ ABI
  // 2.5.2) with virtual bases only, whose vtable holds just their offsets
  std::vector<irep_idt> classes_with_vtable;
  {
    std::set<irep_idt> seen;
    std::vector<irep_idt> work{symbol.name};
    while(!work.empty())
    {
      const irep_idt c = work.back();
      work.pop_back();
      if(!seen.insert(c).second)
        continue;
      if(symbol_table.has_symbol("virtual_table::" + id2string(c)))
        classes_with_vtable.push_back(c);
      const symbolt *sym = symbol_table.lookup(c);
      if(sym == nullptr || sym->type.id() != ID_struct)
        continue;
      for(const auto &base : to_struct_type(sym->type).bases())
        if(base.type().id() == ID_struct_tag)
          work.push_back(to_struct_tag_type(base.type()).get_identifier());
    }
  }

  for(const irep_idt &class_id : classes_with_vtable)
  {
    const symbolt &late_cast_symb = lookup(class_id);
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

  // Itanium C++ ABI 2.6.2 (construction vtables), for the direct bases that
  // have virtual bases: while such a base subobject is constructed or
  // destroyed, its virtual pointers must point to tables with the BASE's
  // overriders (N5008 [class.cdtor]/4) but THIS complete object's virtual
  // base offsets.  One object per (vtable struct X of the base's hierarchy,
  // base B): `virtual_table::X@B@D', a copy of the base's complete-object
  // table `virtual_table::X@B'; set_virtual_base_offsets fills in the
  // offsets.  A base without virtual bases needs none: its own tables
  // serve, and its constructor installs them itself.
  // collected first: inserting into the symbol table (an unordered map)
  // while iterating over it invalidates the iterator on a rehash, and
  // tables were skipped
  std::vector<symbolt> construction_tables;
  for(const irep_idt &base_id : construction_vtable_bases(symbol.name))
  {
    for(const auto &named : symbol_table.symbols)
    {
      const std::string name = id2string(named.first);
      const std::string suffix = "@" + id2string(base_id);
      if(
        name.compare(0, 15, "virtual_table::") != 0 ||
        name.size() <= suffix.size() ||
        name.compare(name.size() - suffix.size(), suffix.size(), suffix) != 0 ||
        named.second.is_type)
      {
        continue;
      }
      // exactly `virtual_table::X@B' (not a construction table `X@Y@B')
      if(std::count(name.begin(), name.end(), '@') != 1)
        continue;
      symbolt construction = named.second;
      construction.name = name + "@" + id2string(symbol.name);
      construction.base_name =
        id2string(named.second.base_name) + "@" + id2string(symbol.base_name);
      construction_tables.push_back(std::move(construction));
    }
  }
  for(auto &construction : construction_tables)
  {
    if(!symbol_table.has_symbol(construction.name))
      symbol_table.insert(std::move(construction));
  }
}

std::vector<irep_idt>
cpp_typecheckt::construction_vtable_bases(const irep_idt &class_id) const
{
  std::vector<irep_idt> result;
  const symbolt *sym = symbol_table.lookup(class_id);
  if(sym == nullptr || sym->type.id() != ID_struct)
    return result;
  for(const auto &base : to_struct_type(sym->type).bases())
  {
    if(base.get_bool(ID_virtual) || base.type().id() != ID_struct_tag)
      continue;
    const irep_idt base_id = to_struct_tag_type(base.type()).get_identifier();
    const symbolt *base_sym = symbol_table.lookup(base_id);
    if(base_sym == nullptr || base_sym->type.id() != ID_struct)
      continue;
    std::list<irep_idt> vbases;
    get_virtual_bases(to_struct_type(base_sym->type), vbases);
    if(!vbases.empty())
      result.push_back(base_id);
  }
  return result;
}

std::vector<std::pair<struct_typet::componentt, exprt>>
cpp_typecheckt::construction_vtable_installs(
  const symbolt &symbol,
  const irep_idt &base_id) const
{
  std::vector<std::pair<struct_typet::componentt, exprt>> result;
  for(auto &pointer : base_subobject_vtable_pointers(symbol, base_id))
  {
    // the table the base's own constructor would install, renamed to the
    // construction table of this complete object
    exprt *object = &to_address_of_expr(pointer.second).object();
    while(object->id() == ID_member)
      object = &to_member_expr(*object).compound();
    const irep_idt construction_name =
      id2string(to_symbol_expr(*object).get_identifier()) + "@" +
      id2string(symbol.name);
    if(!symbol_table.has_symbol(construction_name))
      continue;
    to_symbol_expr(*object).set_identifier(construction_name);
    result.push_back(std::move(pointer));
  }
  return result;
}

std::vector<std::pair<struct_typet::componentt, exprt>>
cpp_typecheckt::base_subobject_vtable_pointers(
  const symbolt &symbol,
  const irep_idt &base_id) const
{
  std::vector<std::pair<struct_typet::componentt, exprt>> result;
  const symbolt *base_sym = symbol_table.lookup(base_id);
  if(symbol.type.id() != ID_struct || base_sym == nullptr)
    return result;
  const struct_typet &struct_type = to_struct_type(symbol.type);
  const struct_typet &base_struct = to_struct_type(base_sym->type);

  // the virtual pointers of the base subobject: those of its non-virtual
  // part (the derived class's components whose subobject path starts with
  // the base, add_base_components; the rest of the path is the one in the
  // base -- a base class occurring twice has renamed pointers in the
  // derived class, [class.mi]/3) and those of its virtual bases
  // (components marked with the virtual base, one of each)
  auto base_component =
    [&](const struct_typet::componentt &c) -> const struct_typet::componentt *
  {
    const irep_idt vb = c.get(ID_C_virtual_base);
    const auto &path = c.find(ID_C_subobject_path).get_sub();
    for(const auto &bc : base_struct.components())
    {
      if(!bc.get_bool(ID_is_vtptr) || bc.get(ID_C_virtual_base) != vb)
        continue;
      if(!vb.empty())
      {
        if(bc.get_name() == c.get_name())
          return &bc;
        continue;
      }
      if(path.empty() || path.front().id() != base_id)
        return nullptr;
      const auto &base_path = bc.find(ID_C_subobject_path).get_sub();
      if(
        base_path.size() + 1 == path.size() &&
        std::equal(
          base_path.begin(),
          base_path.end(),
          std::next(path.begin()),
          [](const irept &x, const irept &y) { return x.id() == y.id(); }))
      {
        return &bc;
      }
    }
    return nullptr;
  };
  std::list<irep_idt> base_vbases;
  get_virtual_bases(base_struct, base_vbases);

  // The virtual bases' pointers first: a member access to one goes through
  // the complete object's vtable, which the non-virtual part's pointer
  // still holds at that point (the installs run in this order).
  for(int pass = 0; pass < 2; ++pass)
    for(const auto &c : struct_type.components())
    {
      if(!c.get_bool(ID_is_vtptr))
        continue;
      const irep_idt vb = c.get(ID_C_virtual_base);
      if(vb.empty() != (pass == 1))
        continue;
      if(
        !vb.empty() && std::find(base_vbases.begin(), base_vbases.end(), vb) ==
                         base_vbases.end())
      {
        continue;
      }
      const struct_typet::componentt *in_base = base_component(c);
      if(in_base == nullptr)
        continue;
      // the table the base's own constructor would install
      exprt value = vtable_pointer_value(*base_sym, *in_base);
      if(value.id() != ID_address_of)
        continue;
      const exprt *object = &to_address_of_expr(value).object();
      while(object->id() == ID_member)
        object = &to_member_expr(*object).compound();
      if(object->id() != ID_symbol)
        continue;
      result.emplace_back(c, value);
    }
  return result;
}

void cpp_typecheckt::typecheck_base_construction_vtables(codet &code)
{
  const source_locationt source_location = code.source_location();
  const irep_idt base_id = code.get(ID_base);
  const bool restore = code.get_bool("#restore");
  // a base without virtual bases installs its own tables: only save and
  // restore the pointers around its construction
  const bool save_only = code.get_bool("#save_only");
  const std::string index = id2string(code.get("#index"));
  code_blockt result;
  result.set_statement(ID_decl_block);
  result.add_source_location() = source_location;

  const exprt this_expr = cpp_scopes.current_scope().this_expr;
  const symbolt *class_symbol = nullptr;
  if(
    this_expr.type().id() == ID_pointer &&
    to_pointer_type(this_expr.type()).base_type().id() == ID_struct_tag)
  {
    class_symbol = symbol_table.lookup(
      to_struct_tag_type(to_pointer_type(this_expr.type()).base_type())
        .get_identifier());
  }
  if(class_symbol == nullptr || class_symbol->type.id() != ID_struct)
  {
    code = std::move(result);
    return;
  }
  exprt most_derived = cpp_namet{"@most_derived", source_location}.as_expr();
  typecheck_expr(most_derived);

  // a virtual pointer of the base subobject: its position depends on the
  // complete object when it lies in a virtual base (reached through the
  // virtual pointers in place, Itanium C++ ABI 2.5.2)
  auto subobject_pointer = [&](const struct_typet::componentt &c) -> exprt
  {
    exprt pointer = this_expr;
    const irep_idt virtual_base = c.get(ID_C_virtual_base);
    if(!virtual_base.empty() && symbol_table.has_symbol(virtual_base))
    {
      make_ptr_typecast(pointer, pointer_type(struct_tag_typet{virtual_base}));
      dereference_exprt object{pointer};
      object.set(ID_C_lvalue, true);
      return member_exprt{object, c.get_name(), c.type()};
    }
    dereference_exprt object{pointer};
    object.set(ID_C_lvalue, true);
    return member_exprt{object, c.get_name(), c.type()};
  };

  auto local = [&](const std::string &name, const typet &type) -> symbol_exprt
  {
    const irep_idt identifier =
      cpp_scopes.current_scope().prefix + "@" + name + "#" + index;
    if(const symbolt *existing = symbol_table.lookup(identifier))
      return existing->symbol_expr();
    symbolt symbol{identifier, type, ID_cpp};
    symbol.base_name = "@" + name;
    symbol.is_lvalue = true;
    symbol.is_file_local = true;
    symbol.is_thread_local = true;
    symbol.location = source_location;
    const symbol_exprt expr = symbol.symbol_expr();
    symbol_table.insert(std::move(symbol));
    return expr;
  };

  code_blockt guarded;
  std::size_t k = 0;
  for(const auto &pointer :
      base_subobject_vtable_pointers(*class_symbol, base_id))
  {
    const struct_typet::componentt &c = pointer.first;
    const std::string number = std::to_string(k++);
    const exprt location = subobject_pointer(c);
    if(restore)
    {
      const symbolt *saved = symbol_table.lookup(
        cpp_scopes.current_scope().prefix + "@saved_vtable_pointer" + number +
        "#" + index);
      // in reverse order: the location of a virtual base's pointer is
      // computed through the non-virtual part's pointer, which must hold
      // this subobject's table again first
      if(saved != nullptr)
      {
        guarded.statements().insert(
          guarded.statements().begin(),
          code_frontend_assignt{location, saved->symbol_expr()});
      }
      continue;
    }
    const auto saved = local("saved_vtable_pointer" + number, c.type());
    // the declarations are not guarded (their scope is the constructor's
    // body); reading the pointers is: when this is the complete object,
    // a virtual base's pointer is located through tables that may not be
    // this class's at this point
    result.add(code_frontend_declt{saved});
    guarded.add(code_frontend_assignt{saved, location});
    if(save_only)
      continue;

    // the base's own table, and the path to the installed part of it
    exprt value = pointer.second;
    exprt *object = &to_address_of_expr(value).object();
    while(object->id() == ID_member)
      object = &to_member_expr(*object).compound();
    const symbolt &table = lookup(to_symbol_expr(*object).get_identifier());
    const auto copy = local("construction_vtable" + number, table.type);
    *object = copy;

    result.add(code_frontend_declt{copy});
    guarded.add(code_frontend_assignt{copy, table.symbol_expr()});

    // the offsets of the virtual bases from the subobject, at every
    // embedding level of the table (set_virtual_base_offsets does the same
    // for the complete object's tables)
    const exprt subobject_start = typecast_exprt{
      address_of_exprt{location}, pointer_type(unsigned_char_type())};
    std::function<void(const exprt &)> patch = [&](const exprt &part)
    {
      if(part.type().id() != ID_struct_tag)
        return;
      const struct_typet &vt_type = follow_tag(to_struct_tag_type(part.type()));
      for(const auto &field : vt_type.components())
      {
        const member_exprt member{part, field.get_name(), field.type()};
        if(field.get_base_name() == "@base")
        {
          patch(member);
          continue;
        }
        const irep_idt vb = field.get(ID_C_virtual_base);
        if(vb.empty() || !symbol_table.has_symbol(vb))
          continue;
        exprt vbase_pointer = this_expr;
        make_ptr_typecast(vbase_pointer, pointer_type(struct_tag_typet{vb}));
        minus_exprt offset{
          typecast_exprt{vbase_pointer, pointer_type(unsigned_char_type())},
          subobject_start};
        offset.type() = pointer_diff_type();
        guarded.add(code_frontend_assignt{
          member, typecast_exprt::conditional_cast(offset, field.type())});
      }
    };
    patch(copy);
    guarded.add(code_frontend_assignt{location, value});
  }

  if(!guarded.statements().empty())
  {
    result.add(code_ifthenelset{not_exprt{most_derived}, std::move(guarded)});
  }
  for(auto &op : result.operands())
    op.add_source_location() = source_location;
  code = std::move(result);
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

  // N5008 [class.mi]/4, [class.virtual]/2: the virtual pointer of a base
  // class subobject that occurs more than once in the lattice (a renamed
  // component, see add_base_components) points to the table of the final
  // overriders in THAT subobject.  When the most derived class declares no
  // overrider of them, those are the final overriders the direct base on the
  // subobject's path has for it: use the table that base's own complete
  // object installs.
  const auto &path = vtptr.find(ID_C_subobject_path).get_sub();
  const irep_idt shared_name = vtable_pointer_component(most_derived.name);
  if(
    !path.empty() && vtptr.get_name() != shared_name &&
    is_repeated_subobject_vtable_pointer(vtptr))
  {
    // the most derived class's own table for the subobject, when it declares
    // overriders (do_repeated_subobject_virtual_tables)
    const symbolt *own = symbol_table.lookup(
      repeated_subobject_vtable_name(most_derived.name, vtptr));
    if(own != nullptr)
      return address_of_exprt(
        own->symbol_expr(), to_pointer_type(vtptr.type()));
    const symbolt *direct_base = symbol_table.lookup(path.front().id());
    if(direct_base == nullptr || direct_base->type.id() != ID_struct)
      return nil_exprt{};
    for(const auto &c : to_struct_type(direct_base->type).components())
    {
      if(!c.get_bool(ID_is_vtptr))
        continue;
      const auto &base_path = c.find(ID_C_subobject_path).get_sub();
      if(
        base_path.size() + 1 != path.size() ||
        !std::equal(base_path.begin(), base_path.end(), path.begin() + 1))
      {
        continue;
      }
      return vtable_pointer_value(*direct_base, c);
    }
    return nil_exprt{};
  }

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

irep_idt cpp_typecheckt::repeated_subobject_vtable_name(
  const irep_idt &most_derived,
  const struct_typet::componentt &vtptr)
{
  const typet &vt_tag = to_pointer_type(vtptr.type()).base_type();
  std::string name = id2string(to_struct_tag_type(vt_tag).get_identifier()) +
                     "@" + id2string(most_derived) + "@";
  for(const auto &step : vtptr.find(ID_C_subobject_path).get_sub())
    name += "/" + id2string(step.id());
  return name;
}

void cpp_typecheckt::do_repeated_subobject_virtual_tables(const symbolt &symbol)
{
  PRECONDITION(symbol.type.id() == ID_struct);
  const struct_typet &struct_type = to_struct_type(symbol.type);
  const namespacet ns(symbol_table);

  // the class's own overriders, by virtual name ([class.virtual]/2: a
  // virtual member function declared in the most derived class is the final
  // overrider in every base class subobject whose function it overrides)
  std::map<irep_idt, const struct_typet::componentt *> overriders;
  for(const auto &c : struct_type.components())
  {
    if(
      c.type().id() == ID_code && !c.get_bool(ID_from_base) &&
      c.get_bool(ID_is_virtual) && c.type().get("#thunk_target").empty())
    {
      overriders[c.get(ID_virtual_name)] = &c;
    }
  }
  if(overriders.empty())
    return;

  for(const auto &vtptr : struct_type.components())
  {
    // a renamed virtual pointer: one of a base class occurring more than
    // once (add_base_components), in the non-virtual part
    if(
      !vtptr.get_bool(ID_is_vtptr) ||
      !is_repeated_subobject_vtable_pointer(vtptr))
    {
      continue;
    }
    const irep_idt vt_name = repeated_subobject_vtable_name(symbol.name, vtptr);
    const auto subobject_offset =
      member_offset(struct_type, vtptr.get_name(), ns);
    if(symbol_table.has_symbol(vt_name))
    {
      // created before the layout was final: the thunks' `this'
      // adjustments are rebuilt with the final subobject offset
      for(const auto &overrider : overriders)
      {
        symbolt *thunk = symbol_table.get_writeable(
          id2string(vt_name) +
          "::" + id2string(overrider.second->get_base_name()));
        if(thunk != nullptr)
        {
          build_this_adjusting_thunk_body(
            *thunk,
            overrider.second->get_name(),
            lookup(overrider.second->get_name()).type,
            subobject_offset);
        }
      }
      continue;
    }

    // start from the table the direct base on the path installs
    const auto &path = vtptr.find(ID_C_subobject_path).get_sub();
    const symbolt *direct_base = symbol_table.lookup(path.front().id());
    if(direct_base == nullptr || direct_base->type.id() != ID_struct)
      continue;
    exprt base_address = nil_exprt{};
    for(const auto &c : to_struct_type(direct_base->type).components())
    {
      const auto &base_path = c.find(ID_C_subobject_path).get_sub();
      if(
        c.get_bool(ID_is_vtptr) && base_path.size() + 1 == path.size() &&
        std::equal(base_path.begin(), base_path.end(), path.begin() + 1))
      {
        base_address = vtable_pointer_value(*direct_base, c);
        break;
      }
    }
    if(base_address.id() != ID_address_of)
      continue;
    // the value of that (possibly embedded) table
    std::vector<irep_idt> members;
    exprt object = to_address_of_expr(base_address).object();
    while(object.id() == ID_member)
    {
      members.push_back(to_member_expr(object).get_component_name());
      object = to_member_expr(object).compound();
    }
    if(object.id() != ID_symbol)
      continue;
    const symbolt *base_table =
      symbol_table.lookup(to_symbol_expr(object).get_identifier());
    if(base_table == nullptr || base_table->value.id() != ID_struct)
      continue;
    exprt value = base_table->value;
    for(auto it = members.rbegin(); it != members.rend(); ++it)
    {
      const struct_typet &t = ns.follow_tag(to_struct_tag_type(value.type()));
      const auto index = t.component_number(*it);
      exprt next = value.operands()[index];
      value = std::move(next);
    }

    // replace the slots the class overrides by thunks that adjust `this'
    // from this subobject to the class
    const struct_typet &vt_type =
      ns.follow_tag(to_struct_tag_type(value.type()));
    std::function<void(exprt &, const struct_typet &)> patch =
      [&](exprt &table, const struct_typet &table_type)
    {
      const auto &comps = table_type.components();
      for(std::size_t i = 0; i < comps.size() && i < table.operands().size();
          ++i)
      {
        if(comps[i].get_base_name() == "@base")
        {
          patch(
            table.operands()[i],
            ns.follow_tag(to_struct_tag_type(comps[i].type())));
          continue;
        }
        const auto it = overriders.find(comps[i].get_base_name());
        if(it == overriders.end())
          continue;
        const struct_typet::componentt &overrider = *it->second;
        const typet &slot_type = to_pointer_type(comps[i].type()).base_type();
        symbolt thunk{
          id2string(vt_name) + "::" + id2string(overrider.get_base_name()),
          slot_type,
          symbol.mode};
        thunk.base_name = overrider.get_base_name();
        thunk.pretty_name = overrider.get_base_name();
        thunk.module = module;
        thunk.location = overrider.source_location();
        code_typet &thunk_type = to_code_type(thunk.type);
        std::size_t n = 0;
        for(auto &parameter : thunk_type.parameters())
        {
          symbolt parameter_symbol{
            id2string(thunk.name) + "::arg" + std::to_string(n++),
            parameter.type(),
            symbol.mode};
          parameter_symbol.base_name = "arg" + std::to_string(n - 1);
          parameter.set_identifier(parameter_symbol.name);
          parameter.set_base_name(parameter_symbol.base_name);
          symbol_table.insert(std::move(parameter_symbol));
        }
        build_this_adjusting_thunk_body(
          thunk,
          overrider.get_name(),
          lookup(overrider.get_name()).type,
          subobject_offset);
        const irep_idt thunk_name = thunk.name;
        symbol_table.insert(std::move(thunk));
        table.operands()[i] = address_of_exprt{
          symbol_exprt{thunk_name, slot_type},
          to_pointer_type(comps[i].type())};
      }
    };
    patch(value, vt_type);

    symbolt vt_object{vt_name, value.type(), symbol.mode};
    vt_object.base_name = vt_name;
    vt_object.module = module;
    vt_object.location = symbol.location;
    vt_object.is_lvalue = true;
    vt_object.is_static_lifetime = true;
    vt_object.value = std::move(value);
    symbol_table.insert(std::move(vt_object));
  }
}
