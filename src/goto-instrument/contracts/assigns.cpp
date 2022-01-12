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

#include <ansi-c/c_expr.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>

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
      "no definite size for lvalue target: \n" + expr.pretty());

    return {typecast_exprt::conditional_cast(
              address_of_exprt{expr}, pointer_type(char_type())),
            typecast_exprt::conditional_cast(size.value(), signed_size_type())};
  }

  UNREACHABLE;
}

/// Normalises a assigns target expression to a guarded slice struct.
///
/// ```
/// case expr of
///  | guard ? target ->
///          {guard
///           target,
///           normalize_to_slice(target)}
///  | target ->
///          {true,
///           target,
///           normalize_to_slice(target)}
/// ```
static const guarded_slicet
normalize_to_guarded_slice(const exprt &expr, const namespacet &ns)
{
  if(can_cast_expr<conditional_target_group_exprt>(expr))
  {
    const auto &conditional_target_group =
      to_conditional_target_group_expr(expr);
    INVARIANT(
      conditional_target_group.targets().size() == 1,
      "expecting only a single target");
    const auto &target = conditional_target_group.targets().front();
    const auto slice = normalize_to_slice(target, ns);
    return {
      conditional_target_group.condition(), target, slice.first, slice.second};
  }
  else
  {
    const auto slice = normalize_to_slice(expr, ns);
    return {true_exprt{}, expr, slice.first, slice.second};
  }
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
    guarded_slice(normalize_to_guarded_slice(expr, parent.ns)),
    validity_condition_var(
      generate_new_symbol("__car_valid", bool_typet(), location).symbol_expr()),
    lower_bound_address_var(generate_new_symbol(
                              "__car_lb",
                              guarded_slice.start_adress.type(),
                              location)
                              .symbol_expr()),
    upper_bound_address_var(generate_new_symbol(
                              "__car_ub",
                              guarded_slice.start_adress.type(),
                              location)
                              .symbol_expr())
{
}

goto_programt
assigns_clauset::conditional_address_ranget::generate_snapshot_instructions(
  check_target_validityt check_target_validity) const
{
  goto_programt instructions;

  // clean up side effects from the guard expression if needed
  cleanert cleaner(parent.symbol_table, parent.log.get_message_handler());
  exprt clean_guard(guarded_slice.guard);

  if(has_subexpr(clean_guard, ID_side_effect))
    cleaner.clean(
      clean_guard,
      instructions,
      parent.symbol_table.lookup_ref(parent.function_name).mode);

  // we want checks on the guard because it is user code
  clean_guard.add_source_location() = location;

  // adding pragmas to the location to selectively disable checks
  // where it is sound to do so
  source_locationt location_no_checks(location);
  disable_pointer_checks(location_no_checks);

  // If requested, we check that when guard condition is true,
  // the target's `start_address` pointer satisfies w_ok with the expected size
  // (or is NULL if we allow it explicitly).
  // This assertion will be falsified whenever `start_address` is invalid or
  // not of the right size (or is NULL if we dot not allow it expliclitly).
  auto validity_check_expr =
    check_target_validity == check_target_validityt::YES_ALLOW_NULL
      ? or_exprt{not_exprt{clean_guard},
                 null_pointer(guarded_slice.start_adress),
                 w_ok_exprt{guarded_slice.start_adress, guarded_slice.size}}
      : or_exprt{not_exprt{clean_guard},
                 w_ok_exprt{guarded_slice.start_adress, guarded_slice.size}};

  if(check_target_validity != check_target_validityt::NO)
  {
    auto target_validity_assert =
      instructions.add(goto_programt::make_assertion(
        simplify_expr(validity_check_expr, parent.ns), location_no_checks));

    target_validity_assert->source_location_nonconst().set_comment(
      "Check assigns target validity '" +
      from_expr(parent.ns, "", guarded_slice.guard) + ": " +
      from_expr(parent.ns, "", guarded_slice.expr) + "'");
  }

  // ~~~ From then on we implicitly assume that the assertion holds ~~~ //

  // We snapshot the validity condition, lower bound and upper bound addresses
  instructions.add(
    goto_programt::make_decl(validity_condition_var, location_no_checks));

  instructions.add(goto_programt::make_assignment(
    validity_condition_var,
    simplify_expr(
      and_exprt{clean_guard,
                not_exprt{null_pointer(guarded_slice.start_adress)}},
      parent.ns),
    location_no_checks));

  instructions.add(
    goto_programt::make_decl(lower_bound_address_var, location_no_checks));

  instructions.add(goto_programt::make_assignment(
    lower_bound_address_var, guarded_slice.start_adress, location_no_checks));

  instructions.add(
    goto_programt::make_decl(upper_bound_address_var, location_no_checks));

  instructions.add(goto_programt::make_assignment(
    upper_bound_address_var,
    simplify_expr(
      plus_exprt{guarded_slice.start_adress, guarded_slice.size}, parent.ns),
    location_no_checks));

  // The snapshot assignments involve only instrumentation variables
  // need not be checked against the surrounding assigns clause.
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

bool assigns_clauset::conditional_address_ranget::maybe_alive(
  cfg_infot &cfg_info) const
{
  if(can_cast_expr<symbol_exprt>(source_expr))
    return cfg_info.is_maybe_alive(to_symbol_expr(source_expr));

  return true;
}

assigns_clauset::assigns_clauset(
  const exprt::operandst &assigns,
  messaget &log,
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
  const conditional_address_ranget &lhs,
  check_target_validityt allow_null_target,
  optionalt<cfg_infot> &cfg_info_opt) const
{
  if(write_set.empty())
  {
    if(allow_null_target == check_target_validityt::YES_ALLOW_NULL)
      return false_exprt{};
    else
      return null_pointer(lhs.guarded_slice.start_adress);
  }

  exprt::operandst conditions;

  if(cfg_info_opt.has_value())
  {
    auto &cfg_info = cfg_info_opt.value();
    for(const auto &target : write_set)
      if(target.maybe_alive(cfg_info))
        conditions.push_back(target.generate_unsafe_inclusion_check(lhs));
  }
  else
  {
    for(const auto &target : write_set)
      conditions.push_back(target.generate_unsafe_inclusion_check(lhs));
  }

  if(allow_null_target == check_target_validityt::YES_ALLOW_NULL)
    return or_exprt{
      null_pointer(lhs.guarded_slice.start_adress),
      and_exprt{lhs.validity_condition_var, disjunction(conditions)}};
  else
    return and_exprt{lhs.validity_condition_var, disjunction(conditions)};
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
