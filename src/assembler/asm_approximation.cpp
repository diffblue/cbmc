/*******************************************************************\

Module: Conservative approximation of inline assembly

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Conservative approximation of inline assembly statements

#include "asm_approximation.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/expr_iterator.h>
#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/symbol_table_base.h>

#include <goto-programs/goto_program.h>

#include <algorithm>

/// \return True iff objects of type \p type cannot be modified.
static bool is_constant_type(const typet &type)
{
  if(type.get_bool(ID_C_constant))
    return true;
  if(type.id() == ID_array)
    return is_constant_type(to_array_type(type).element_type());
  return false;
}

/// \return True iff objects of type \p type can be assigned a value as a
///   whole.
static bool is_complete_type(const typet &type, const namespacet &ns)
{
  if(type.id() == ID_code || type.id() == ID_empty)
    return false;
  if(type.id() == ID_array)
  {
    const array_typet &array_type = to_array_type(type);
    return array_type.size().is_not_nil() &&
           is_complete_type(array_type.element_type(), ns);
  }
  if(type.id() == ID_struct_tag)
    return !ns.follow_tag(to_struct_tag_type(type)).is_incomplete();
  if(type.id() == ID_union_tag)
    return !ns.follow_tag(to_union_tag_type(type)).is_incomplete();
  return true;
}

/// \return True iff the address of lvalue \p expr does not depend on the
///   program state.
static bool has_constant_address(const exprt &expr)
{
  if(expr.id() == ID_symbol)
    return true;
  if(expr.id() == ID_member)
    return has_constant_address(to_member_expr(expr).struct_op());
  if(expr.id() == ID_index)
  {
    const index_exprt &index = to_index_expr(expr);
    return index.index().is_constant() && has_constant_address(index.array());
  }
  return false;
}

void asm_approximationt::collect_addresses(
  const exprt &expr,
  const namespacet &ns,
  std::vector<exprt> &dest)
{
  // look through casts of pointers to integers, as in (uintptr_t)&x
  const exprt &e = expr.type().id() == ID_pointer ? expr : skip_typecast(expr);
  const typet &type = e.type();

  if(type.id() == ID_pointer)
  {
    const typet &base_type = to_pointer_type(type).base_type();
    if(base_type.id() != ID_code && !is_constant_type(base_type))
      dest.push_back(e);
  }
  else if(type.id() == ID_array)
  {
    // the array decays to the address of its first element
    if(!is_constant_type(type))
    {
      dest.push_back(
        address_of_exprt{index_exprt{e, from_integer(0, c_index_type())}});
    }
  }
  else if(type.id() == ID_struct_tag || type.id() == ID_union_tag)
  {
    const struct_union_typet &struct_union_type =
      type.id() == ID_struct_tag ? static_cast<const struct_union_typet &>(
                                     ns.follow_tag(to_struct_tag_type(type)))
                                 : static_cast<const struct_union_typet &>(
                                     ns.follow_tag(to_union_tag_type(type)));
    for(const auto &component : struct_union_type.components())
    {
      const typet &component_type = component.type();
      if(
        component_type.id() == ID_pointer ||
        component_type.id() == ID_struct_tag ||
        component_type.id() == ID_union_tag)
      {
        collect_addresses(member_exprt{e, component}, ns, dest);
      }
    }
  }
}

std::vector<symbol_exprt> asm_approximationt::address_taken_locals(
  const goto_programt &body,
  const namespacet &ns)
{
  std::vector<symbol_exprt> result;

  auto collect = [&result, &ns](const exprt &root)
  {
    for(auto it = root.depth_cbegin(); it != root.depth_cend(); ++it)
    {
      if(it->id() != ID_address_of)
        continue;

      const exprt *object = &to_address_of_expr(*it).object();
      while(object->id() == ID_member || object->id() == ID_index ||
            object->id() == ID_typecast ||
            object->id() == ID_byte_extract_little_endian ||
            object->id() == ID_byte_extract_big_endian)
      {
        object = &object->operands().front();
      }

      if(object->id() != ID_symbol)
        continue;

      const symbolt *symbol = nullptr;
      if(ns.lookup(to_symbol_expr(*object).get_identifier(), symbol))
        continue;

      if(
        !symbol->is_static_lifetime && symbol->is_lvalue &&
        !is_constant_type(symbol->type) && is_complete_type(symbol->type, ns))
      {
        result.push_back(to_symbol_expr(*object));
      }
    }
  };

  for(const auto &instruction : body.instructions)
  {
    collect(instruction.code());
    if(instruction.has_condition())
      collect(instruction.condition());
  }

  auto by_name = [](const symbol_exprt &a, const symbol_exprt &b)
  { return id2string(a.get_identifier()) < id2string(b.get_identifier()); };
  std::sort(result.begin(), result.end(), by_name);
  result.erase(std::unique(result.begin(), result.end()), result.end());

  return result;
}

const std::vector<symbol_exprt> &asm_approximationt::get_static_objects()
{
  if(static_objects.has_value())
    return *static_objects;

  const namespacet ns{symbol_table};
  static_objects = std::vector<symbol_exprt>{};
  for(const auto &entry : symbol_table.symbols)
  {
    const symbolt &symbol = entry.second;
    if(
      !symbol.is_static_lifetime || symbol.is_type || symbol.is_macro ||
      !symbol.is_lvalue || is_constant_type(symbol.type) ||
      !is_complete_type(symbol.type, ns) ||
      symbol.name.starts_with(CPROVER_PREFIX) ||
      symbol.base_name.starts_with(CPROVER_PREFIX))
    {
      continue;
    }

    static_objects->push_back(symbol.symbol_expr());
  }

  std::sort(
    static_objects->begin(),
    static_objects->end(),
    [](const symbol_exprt &a, const symbol_exprt &b)
    { return id2string(a.get_identifier()) < id2string(b.get_identifier()); });

  return *static_objects;
}

/// Appends to \p dest an assignment of a nondeterministic value to \p lvalue.
static void havoc_lvalue(
  const exprt &lvalue,
  const source_locationt &source_location,
  goto_programt &dest)
{
  dest.add(goto_programt::make_assignment(
    lvalue,
    side_effect_expr_nondett{lvalue.type(), source_location},
    source_location));
}

/// Appends to \p dest instructions that assign a nondeterministic value to the
/// object \p pointer points to, unless \p pointer is null.
static void havoc_pointee(
  const exprt &pointer,
  const source_locationt &source_location,
  goto_programt &dest)
{
  const null_pointer_exprt null{to_pointer_type(pointer.type())};
  auto skip = dest.add(goto_programt::make_incomplete_goto(
    equal_exprt{pointer, null}, source_location));

  const codet havoc{ID_havoc_object, {pointer}, source_location};
  dest.add(goto_programt::make_other(havoc, source_location));

  skip->complete_goto(dest.add(goto_programt::make_skip(source_location)));
}

void asm_approximationt::operator()(
  const asm_footprintt &footprint,
  const std::vector<symbol_exprt> &address_taken_locals,
  const irep_idt &function_id,
  const source_locationt &source_location,
  goto_programt &dest)
{
  const namespacet ns{symbol_table};
  std::vector<symbol_exprt> temporaries;

  // 1. the statement reads its inputs
  for(const auto &read : footprint.reads)
  {
    code_expressiont evaluate{read};
    evaluate.add_source_location() = source_location;
    dest.add(goto_programt::make_other(evaluate, source_location));
  }

  // 2. record the values of addresses before any of them is changed, as the
  // instructions below may change the objects these are stored in
  auto snapshot = [&](const exprt &value) -> exprt
  {
    const symbolt &tmp = get_fresh_aux_symbol(
      value.type(),
      id2string(function_id),
      "asm_address",
      source_location,
      ID_C,
      symbol_table);
    const symbol_exprt tmp_expr = tmp.symbol_expr();
    temporaries.push_back(tmp_expr);
    dest.add(goto_programt::make_decl(tmp_expr, source_location));
    dest.add(goto_programt::make_assignment(tmp_expr, value, source_location));
    return tmp_expr;
  };

  // pointers, and the values of the pointers stored in objects of static
  // lifetime if the statement may access arbitrary memory
  std::vector<exprt> addresses = footprint.addresses;
  if(footprint.arbitrary_memory)
  {
    for(const auto &object : get_static_objects())
    {
      if(object.type().id() != ID_array)
        collect_addresses(object, ns, addresses);
    }
  }

  std::vector<exprt> pointers;
  for(const auto &address : addresses)
  {
    if(address.id() == ID_address_of)
    {
      const exprt &object = to_address_of_expr(address).object();
      if(has_constant_address(object))
      {
        pointers.push_back(address);
        continue;
      }
    }
    pointers.push_back(snapshot(address));
  }

  // the lvalues written, with addresses evaluated before the statement; for
  // bit fields, whose address cannot be taken, record the address of the
  // enclosing object
  std::vector<exprt> writes;
  for(const auto &write : footprint.writes)
  {
    exprt lvalue = write;
    std::vector<member_exprt> bit_field_members;
    while(lvalue.id() == ID_member && lvalue.type().id() == ID_c_bit_field)
    {
      bit_field_members.push_back(to_member_expr(lvalue));
      lvalue = to_member_expr(lvalue).struct_op();
    }

    if(!has_constant_address(lvalue))
      lvalue = dereference_exprt{snapshot(address_of_exprt{lvalue})};

    for(auto it = bit_field_members.rbegin(); it != bit_field_members.rend();
        ++it)
    {
      lvalue = member_exprt{lvalue, it->get_component_name(), it->type()};
    }
    writes.push_back(lvalue);
  }

  // 3. the objects pointed to
  for(const auto &pointer : pointers)
    havoc_pointee(pointer, source_location, dest);

  // 4. arbitrary memory: what the statement can name
  if(footprint.arbitrary_memory)
  {
    for(const auto &object : get_static_objects())
      havoc_lvalue(object, source_location, dest);
    for(const auto &local : address_taken_locals)
      havoc_lvalue(local, source_location, dest);
  }

  // 5. the outputs
  for(const auto &write : writes)
    havoc_lvalue(write, source_location, dest);

  // 6. the floating-point rounding mode, which the statement may change via
  // the control registers of the floating-point unit
  const symbolt *rounding_mode = nullptr;
  if(!ns.lookup(CPROVER_PREFIX "rounding_mode", rounding_mode))
  {
    const symbol_exprt rounding_mode_expr = rounding_mode->symbol_expr();
    havoc_lvalue(rounding_mode_expr, source_location, dest);
    const typet &type = rounding_mode_expr.type();
    dest.add(goto_programt::make_assumption(
      and_exprt{
        binary_relation_exprt{rounding_mode_expr, ID_ge, from_integer(0, type)},
        binary_relation_exprt{
          rounding_mode_expr, ID_le, from_integer(3, type)}},
      source_location));
  }

  for(auto it = temporaries.rbegin(); it != temporaries.rend(); ++it)
    dest.add(goto_programt::make_dead(*it, source_location));
}
