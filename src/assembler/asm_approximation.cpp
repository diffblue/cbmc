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
#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/symbol.h>

#include <goto-programs/goto_program.h>

/// \return True iff objects of type \p type cannot be modified.
static bool is_constant_type(const typet &type)
{
  if(type.get_bool(ID_C_constant))
    return true;
  if(type.id() == ID_array)
    return is_constant_type(to_array_type(type).element_type());
  return false;
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

void asm_approximationt::operator()(
  const asm_footprintt &footprint,
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

  // 2. the lvalues written, with addresses evaluated before the statement
  // changes any object; for bit fields, whose address cannot be taken, record
  // the address of the enclosing object
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
    {
      const exprt address = address_of_exprt{lvalue};
      const symbol_exprt tmp = get_fresh_aux_symbol(
                                 address.type(),
                                 id2string(function_id),
                                 "asm_address",
                                 source_location,
                                 ID_C,
                                 symbol_table)
                                 .symbol_expr();
      temporaries.push_back(tmp);
      dest.add(goto_programt::make_decl(tmp, source_location));
      dest.add(goto_programt::make_assignment(tmp, address, source_location));
      lvalue = dereference_exprt{tmp};
    }

    for(auto it = bit_field_members.rbegin(); it != bit_field_members.rend();
        ++it)
    {
      lvalue = member_exprt{lvalue, it->get_component_name(), it->type()};
    }
    writes.push_back(lvalue);
  }

  // 3. the objects reachable from the addresses and, for arbitrary memory
  // accesses, from what the statement can name
  if(!footprint.addresses.empty() || footprint.arbitrary_memory)
  {
    codet havoc{ID_havoc_reachable, footprint.addresses, source_location};
    if(footprint.arbitrary_memory)
      havoc.set(ID_arbitrary_memory, true);
    dest.add(goto_programt::make_other(havoc, source_location));
  }

  // 4. the outputs, and whether and where the statement jumps
  for(const auto &write : writes)
    havoc_lvalue(write, source_location, dest);
  if(footprint.goto_target.has_value())
    havoc_lvalue(*footprint.goto_target, source_location, dest);

  // 5. the floating-point rounding mode, which the statement may change via
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
