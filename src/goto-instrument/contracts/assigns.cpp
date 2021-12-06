/*******************************************************************\

Module: Specify write set in code contracts.

Author: Felipe R. Monteiro

Date: July 2021

\*******************************************************************/

/// \file
/// Specify write set in code contracts

#include "assigns.h"
#include "utils.h"

#include <analyses/call_graph.h>

#include <langapi/language_util.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>

static const slicet normalize_to_slice(const exprt &expr, const namespacet &ns)
{
  // FIXME: Refactor these checks out to a common function that can be
  // used both in compilation and instrumentation stages
  if(expr.id() == ID_pointer_object)
  {
    const auto &arg = expr.operands().front();
    return {
      minus_exprt{
        typecast_exprt::conditional_cast(arg, pointer_type(char_type())),
        pointer_offset(arg)},
      typecast_exprt::conditional_cast(object_size(arg), signed_size_type())};
  }
  else if(is_assignable(expr))
  {
    const auto &size = size_of_expr(expr.type(), ns);

    INVARIANT(
      size.has_value(),
      "`sizeof` must always be computable on l-value assigns clause targets.");

    return {typecast_exprt::conditional_cast(
              address_of_exprt{expr}, pointer_type(char_type())),
            typecast_exprt::conditional_cast(size.value(), signed_size_type())};
  }

  UNREACHABLE;
}

const symbolt assigns_clauset::conditional_address_ranget::generate_new_symbol(
  const std::string &prefix,
  const typet &type,
  const source_locationt &location) const
{
  return new_tmp_symbol(
    type,
    location,
    parent.symbol_table.lookup_ref(parent.function_name).mode,
    parent.symbol_table,
    prefix);
}

assigns_clauset::conditional_address_ranget::conditional_address_ranget(
  const assigns_clauset &parent,
  const exprt &expr)
  : source_expr(expr),
    location(expr.source_location()),
    parent(parent),
    slice(normalize_to_slice(expr, parent.ns)),
    validity_condition_var(
      generate_new_symbol("__car_valid", bool_typet(), location).symbol_expr()),
    lower_bound_address_var(
      generate_new_symbol("__car_lb", slice.first.type(), location)
        .symbol_expr()),
    upper_bound_address_var(
      generate_new_symbol("__car_ub", slice.first.type(), location)
        .symbol_expr())
{
}

goto_programt
assigns_clauset::conditional_address_ranget::generate_snapshot_instructions()
  const
{
  goto_programt instructions;
  // adding pragmas to the location to selectively disable checks
  // where it is sound to do so
  source_locationt location_no_checks = location;
  disable_pointer_checks(location_no_checks);

  instructions.add(
    goto_programt::make_decl(validity_condition_var, location_no_checks));
  instructions.add(
    goto_programt::make_decl(lower_bound_address_var, location_no_checks));
  instructions.add(
    goto_programt::make_decl(upper_bound_address_var, location_no_checks));

  instructions.add(goto_programt::make_assignment(
    lower_bound_address_var,
    null_pointer_exprt{to_pointer_type(slice.first.type())},
    location_no_checks));
  instructions.add(goto_programt::make_assignment(
    upper_bound_address_var,
    null_pointer_exprt{to_pointer_type(slice.first.type())},
    location_no_checks));

  goto_programt skip_program;
  const auto skip_target =
    skip_program.add(goto_programt::make_skip(location_no_checks));

  const auto validity_check_expr =
    and_exprt{all_dereferences_are_valid(source_expr, parent.ns),
              w_ok_exprt{slice.first, slice.second}};
  instructions.add(goto_programt::make_assignment(
    validity_condition_var, validity_check_expr, location_no_checks));

  instructions.add(goto_programt::make_goto(
    skip_target, not_exprt{validity_condition_var}, location_no_checks));

  instructions.add(goto_programt::make_assignment(
    lower_bound_address_var, slice.first, location_no_checks));

  // the computation of the CAR upper bound can overflow into the object ID bits
  // of the pointer with very large allocation sizes.
  // We enable pointer overflow checks to detect such cases.
  source_locationt location_overflow_check = location;
  location_overflow_check.add_pragma("enable:pointer-overflow-check");

  instructions.add(goto_programt::make_assignment(
    upper_bound_address_var,
    plus_exprt{slice.first, slice.second},
    location_overflow_check));
  instructions.destructive_append(skip_program);

  // The assignments above are only performed on locally defined temporaries
  // and need not be checked for inclusion in the enclosing scope's write set.
  add_pragma_disable_assigns_check(instructions);
  return instructions;
}

const exprt
assigns_clauset::conditional_address_ranget::generate_unsafe_inclusion_check(
  const conditional_address_ranget &lhs) const
{
  // remark: both lb and ub are derived from the same object so checking
  // same_object(upper_bound_address_var, lhs.upper_bound_address_var)
  // is redundant
  return conjunction(
    {validity_condition_var,
     same_object(lower_bound_address_var, lhs.lower_bound_address_var),
     less_than_or_equal_exprt{pointer_offset(lower_bound_address_var),
                              pointer_offset(lhs.lower_bound_address_var)},
     less_than_or_equal_exprt{pointer_offset(lhs.upper_bound_address_var),
                              pointer_offset(upper_bound_address_var)}});
}

assigns_clauset::assigns_clauset(
  const exprt::operandst &assigns,
  const messaget &log,
  const namespacet &ns,
  const irep_idt &function_name,
  symbol_tablet &symbol_table)
  : log(log), ns(ns), function_name(function_name), symbol_table(symbol_table)
{
  for(const auto &target_expr : assigns)
    add_to_write_set(target_expr);
}

assigns_clauset::write_sett::const_iterator
assigns_clauset::add_to_write_set(const exprt &target_expr)
{
  auto result = write_set.emplace(*this, target_expr);

  if(!result.second)
  {
    log.warning() << "Ignored duplicate expression '"
                  << from_expr(ns, target_expr.id(), target_expr)
                  << "' in assigns clause at "
                  << target_expr.source_location().as_string() << messaget::eom;
  }
  return result.first;
}

void assigns_clauset::remove_from_write_set(const exprt &target_expr)
{
  write_set.erase(conditional_address_ranget(*this, target_expr));
}

exprt assigns_clauset::generate_inclusion_check(
  const conditional_address_ranget &lhs) const
{
  if(write_set.empty())
    return not_exprt{lhs.validity_condition_var};

  exprt::operandst conditions{not_exprt{lhs.validity_condition_var}};
  for(const auto &target : write_set)
    conditions.push_back(target.generate_unsafe_inclusion_check(lhs));

  return disjunction(conditions);
}

void havoc_assigns_targetst::append_havoc_code_for_expr(
  const source_locationt location,
  const exprt &expr,
  goto_programt &dest) const
{
  if(expr.id() == ID_pointer_object)
  {
    append_object_havoc_code_for_expr(location, expr.operands().front(), dest);
    return;
  }

  havoc_utilst::append_havoc_code_for_expr(location, expr, dest);
}

void assigns_clauset::add_static_locals_to_write_set(
  const goto_functionst &functions,
  const irep_idt &root_function)
{
  auto call_graph =
    call_grapht::create_from_root_function(functions, root_function, true)
      .get_directed_graph();

  for(const auto &sym_pair : symbol_table)
  {
    const auto &sym = sym_pair.second;
    if(sym.is_static_lifetime)
    {
      auto fname = sym.location.get_function();
      if(
        !fname.empty() && (fname == root_function ||
                           call_graph.get_node_index(fname).has_value()))
      {
        // We found a symbol with
        // - a static lifetime
        // - non empty location function
        // - this function appears in the call graph of the function
        add_to_write_set(sym.symbol_expr());
      }
    }
  }
}
