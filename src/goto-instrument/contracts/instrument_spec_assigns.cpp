/*******************************************************************\

Module: Instrument assigns clauses in code contracts.

Author: Remi Delmas

Date: January 2022

\*******************************************************************/

/// \file
/// Specify write set in code contracts

#include "instrument_spec_assigns.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/format_expr.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>

#include <analyses/call_graph.h>

#include <langapi/language_util.h>

#include "utils.h"

///// PUBLIC METHODS /////

void instrument_spec_assignst::track_spec_target(
  const exprt &expr,
  goto_programt &dest)
{
  if(auto target = expr_try_dynamic_cast<conditional_target_group_exprt>(expr))
    track_spec_target_group(*target, dest);
  else
    track_plain_spec_target(expr, dest);
}

void instrument_spec_assignst::track_stack_allocated(
  const symbol_exprt &symbol_expr,
  goto_programt &dest)
{
  create_snapshot(create_car_from_stack_alloc(symbol_expr), dest);
}

bool instrument_spec_assignst::stack_allocated_is_tracked(
  const symbol_exprt &symbol_expr) const
{
  return from_stack_alloc.find(symbol_expr) != from_stack_alloc.end();
}

void instrument_spec_assignst::invalidate_stack_allocated(
  const symbol_exprt &symbol_expr,
  goto_programt &dest)
{
  // ensure it is tracked
  PRECONDITION_WITH_DIAGNOSTICS(
    stack_allocated_is_tracked(symbol_expr),
    "symbol is not tracked :" + from_expr(ns, "", symbol_expr));

  const auto &car = from_stack_alloc.find(symbol_expr)->second;

  source_locationt source_location(symbol_expr.source_location());
  add_pragma_disable_pointer_checks(source_location);
  add_pragma_disable_assigns_check(source_location);

  dest.add(goto_programt::make_assignment(
    car.valid_var(), false_exprt{}, source_location));
}

void instrument_spec_assignst::track_heap_allocated(
  const exprt &expr,
  goto_programt &dest)
{
  create_snapshot(create_car_from_heap_alloc(expr), dest);
}

void instrument_spec_assignst::check_inclusion_assignment(
  const exprt &lhs,
  optionalt<cfg_infot> &cfg_info_opt,
  goto_programt &dest)
{
  // create temporary car but do not track
  const auto car = create_car_expr(true_exprt{}, lhs);
  create_snapshot(car, dest);
  inclusion_check_assertion(car, false, true, cfg_info_opt, dest);
}

void instrument_spec_assignst::track_static_locals(goto_programt &dest)
{
  auto call_graph =
    call_grapht::create_from_root_function(functions, function_id, true)
      .get_directed_graph();

  for(const auto &sym_pair : st)
  {
    const auto &sym = sym_pair.second;
    if(sym.is_static_lifetime)
    {
      auto fname = sym.location.get_function();
      if(
        !fname.empty() &&
        (fname == function_id || call_graph.get_node_index(fname).has_value()))
      {
        // We found a symbol with
        // - a static lifetime
        // - non empty location function
        // - this function appears in the call graph of the function

        // insert in tracking set and generate snapshot instructions
        // for this target.
        create_snapshot(create_car_from_stack_alloc(sym.symbol_expr()), dest);
      }
    }
  }
}

void instrument_spec_assignst::
  check_inclusion_heap_allocated_and_invalidate_aliases(
    const exprt &expr,
    optionalt<cfg_infot> &cfg_info_opt,
    goto_programt &dest)
{
  // create temporary car but do not track
  const auto car = create_car_expr(true_exprt{}, expr);

  // generate snapshot instructions for this target.
  create_snapshot(car, dest);

  // check inclusion, allowing null and not allowing stack allocated locals
  inclusion_check_assertion(car, true, false, cfg_info_opt, dest);

  // invalidate aliases of the freed object
  invalidate_heap_and_spec_aliases(car, dest);
}

///// PRIVATE METHODS /////

void instrument_spec_assignst::track_spec_target_group(
  const conditional_target_group_exprt &group,
  goto_programt &dest)
{
  // clean up side effects from the guard expression if needed
  cleanert cleaner(st, log.get_message_handler());
  exprt condition(group.condition());
  if(has_subexpr(condition, ID_side_effect))
    cleaner.clean(condition, dest, st.lookup_ref(function_id).mode);

  // create conditional address ranges by distributing the condition
  for(const auto &target : group.targets())
  {
    // insert in tracking set
    const auto &car = create_car_from_spec_assigns(condition, target);

    // generate target validity check for this target.
    target_validity_assertion(car, true, dest);

    // generate snapshot instructions for this target.
    create_snapshot(car, dest);
  }
}

void instrument_spec_assignst::track_plain_spec_target(
  const exprt &expr,
  goto_programt &dest)
{
  // insert in tracking set
  const auto &car = create_car_from_spec_assigns(true_exprt{}, expr);

  // generate target validity check for this target.
  target_validity_assertion(car, true, dest);

  // generate snapshot instructions for this target.
  create_snapshot(car, dest);
}

const symbolt instrument_spec_assignst::create_fresh_symbol(
  const std::string &suffix,
  const typet &type,
  const source_locationt &location) const
{
  return new_tmp_symbol(
    type, location, st.lookup_ref(function_id).mode, st, suffix);
}

car_exprt instrument_spec_assignst::create_car_expr(
  const exprt &condition,
  const exprt &target) const
{
  const source_locationt &source_location = target.source_location();
  const auto &valid_var =
    create_fresh_symbol("__car_valid", bool_typet(), source_location)
      .symbol_expr();

  const auto &lower_bound_var =
    create_fresh_symbol("__car_lb", pointer_type(char_type()), source_location)
      .symbol_expr();

  const auto &upper_bound_var =
    create_fresh_symbol("__car_ub", pointer_type(char_type()), source_location)
      .symbol_expr();

  if(target.id() == ID_pointer_object)
  {
    const auto &arg = to_unary_expr(target).op();
    return {
      condition,
      target,
      minus_exprt(
        typecast_exprt::conditional_cast(arg, pointer_type(char_type())),
        pointer_offset(arg)),
      typecast_exprt::conditional_cast(object_size(arg), signed_size_type()),
      valid_var,
      lower_bound_var,
      upper_bound_var};
  }
  else if(is_assignable(target))
  {
    const auto &size = size_of_expr(target.type(), ns);

    INVARIANT(
      size.has_value(),
      "no definite size for lvalue target:\n" + target.pretty());

    return {condition,
            target,
            typecast_exprt::conditional_cast(
              address_of_exprt{target}, pointer_type(char_type())),
            typecast_exprt::conditional_cast(size.value(), signed_size_type()),
            valid_var,
            lower_bound_var,
            upper_bound_var};
  };

  UNREACHABLE;
}

void instrument_spec_assignst::create_snapshot(
  const car_exprt &car,
  goto_programt &dest) const
{
  source_locationt source_location(car.source_location());
  add_pragma_disable_pointer_checks(source_location);
  add_pragma_disable_assigns_check(source_location);

  dest.add(goto_programt::make_decl(car.valid_var(), source_location));

  dest.add(goto_programt::make_assignment(
    car.valid_var(),
    simplify_expr(
      and_exprt{car.condition(),
                not_exprt{null_pointer(car.target_start_address())}},
      ns),
    source_location));

  dest.add(goto_programt::make_decl(car.lower_bound_var(), source_location));

  dest.add(goto_programt::make_assignment(
    car.lower_bound_var(), car.target_start_address(), source_location));

  dest.add(goto_programt::make_decl(car.upper_bound_var(), source_location));

  dest.add(goto_programt::make_assignment(
    car.upper_bound_var(),
    simplify_expr(
      plus_exprt{car.target_start_address(), car.target_size()}, ns),
    source_location));
}

exprt instrument_spec_assignst::target_validity_expr(
  const car_exprt &car,
  bool allow_null_target) const
{
  // If requested, we check that when guard condition is true,
  // the target's `start_address` pointer satisfies w_ok with the expected size
  // (or is NULL if we allow it explicitly).
  // This assertion will be falsified whenever `start_address` is invalid or
  // not of the right size (or is NULL if we dot not allow it expliclitly).
  auto result =
    or_exprt{not_exprt{car.condition()},
             w_ok_exprt{car.target_start_address(), car.target_size()}};

  if(allow_null_target)
    result.add_to_operands(null_pointer(car.target_start_address()));

  return simplify_expr(result, ns);
}

void instrument_spec_assignst::target_validity_assertion(
  const car_exprt &car,
  bool allow_null_target,
  goto_programt &dest) const
{
  // since assigns clauses are declared outside of their function body
  // their source location might not have a function attribute
  source_locationt source_location(car.source_location());
  if(source_location.get_function().empty())
    source_location.set_function(function_id);

  source_location.set_property_class("assigns");

  add_pragma_disable_pointer_checks(source_location);
  add_pragma_disable_assigns_check(source_location);

  std::string comment = "Check that ";
  comment += from_expr(ns, "", car.target());
  comment += " is valid";
  if(!car.condition().is_true())
  {
    comment += " when ";
    comment += from_expr(ns, "", car.condition());
  }

  source_location.set_comment(comment);

  dest.add(goto_programt::make_assertion(
    target_validity_expr(car, allow_null_target), source_location));
}

void instrument_spec_assignst::inclusion_check_assertion(
  const car_exprt &car,
  bool allow_null_lhs,
  bool include_stack_allocated,
  optionalt<cfg_infot> &cfg_info_opt,
  goto_programt &dest) const
{
  source_locationt source_location(car.source_location());

  // since assigns clauses are declared outside of their function body
  // their source location might not have a function attribute
  if(source_location.get_function().empty())
    source_location.set_function(function_id);

  add_pragma_disable_pointer_checks(source_location);
  add_pragma_disable_assigns_check(source_location);

  source_location.set_property_class("assigns");

  const auto &orig_comment = source_location.get_comment();
  std::string comment = "Check that ";
  if(!is_assigns_clause_replacement_tracking_comment(orig_comment))
  {
    if(!car.condition().is_true())
      comment += from_expr(ns, "", car.condition()) + ": ";
    comment += from_expr(ns, "", car.target());
  }
  else
    comment += id2string(orig_comment);

  comment += " is assignable";
  source_location.set_comment(comment);

  dest.add(goto_programt::make_assertion(
    inclusion_check_full(
      car, allow_null_lhs, include_stack_allocated, cfg_info_opt),
    source_location));
}

exprt instrument_spec_assignst::inclusion_check_single(
  const car_exprt &car,
  const car_exprt &candidate_car) const
{
  // remark: both lb and ub are derived from the same object so checking
  // same_object(upper_bound_address_var, lhs.upper_bound_address_var)
  // is redundant
  return simplify_expr(
    and_exprt{
      {candidate_car.valid_var(),
       same_object(candidate_car.lower_bound_var(), car.lower_bound_var()),
       less_than_or_equal_exprt{pointer_offset(candidate_car.lower_bound_var()),
                                pointer_offset(car.lower_bound_var())},
       less_than_or_equal_exprt{
         pointer_offset(car.upper_bound_var()),
         pointer_offset(candidate_car.upper_bound_var())}}},
    ns);
}

exprt instrument_spec_assignst::inclusion_check_full(
  const car_exprt &car,
  bool allow_null_lhs,
  bool include_stack_allocated,
  optionalt<cfg_infot> &cfg_info_opt) const
{
  bool no_targets = from_spec_assigns.empty() && from_heap_alloc.empty() &&
                    (!include_stack_allocated || from_stack_alloc.empty());

  // inclusion check expression
  if(no_targets)
  {
    // if null lhs are allowed then we should have a null lhs when
    // we reach this program point, otherwise we should never reach
    // this program point
    if(allow_null_lhs)
      return null_pointer(car.target_start_address());
    else
      return false_exprt{};
  }

  // Build a disjunction over all tracked locations
  exprt::operandst disjuncts;

  for(const auto &pair : from_spec_assigns)
    disjuncts.push_back(inclusion_check_single(car, pair.second));

  for(const auto &pair : from_heap_alloc)
    disjuncts.push_back(inclusion_check_single(car, pair.second));

  if(include_stack_allocated)
  {
    for(const auto &pair : from_stack_alloc)
    {
      // skip dead targets
      if(
        cfg_info_opt.has_value() &&
        !cfg_info_opt.value().is_maybe_alive(pair.first))
        continue;

      disjuncts.push_back(inclusion_check_single(car, pair.second));
    }
  }

  if(allow_null_lhs)
    return or_exprt{null_pointer(car.target_start_address()),
                    and_exprt{car.valid_var(), disjunction(disjuncts)}};
  else
    return and_exprt{car.valid_var(), disjunction(disjuncts)};
}

const car_exprt &instrument_spec_assignst::create_car_from_spec_assigns(
  const exprt &condition,
  const exprt &target)
{
  conditional_target_exprt key{condition, target};
  const auto &found = from_spec_assigns.find(key);
  if(found != from_spec_assigns.end())
  {
    log.warning() << "Ignored duplicate expression '"
                  << from_expr(ns, target.id(), target)
                  << "' in assigns clause spec at "
                  << target.source_location().as_string() << messaget::eom;
    return found->second;
  }
  else
  {
    from_spec_assigns.insert({key, create_car_expr(condition, target)});
    return from_spec_assigns.find(key)->second;
  }
}

const car_exprt &instrument_spec_assignst::create_car_from_stack_alloc(
  const symbol_exprt &target)
{
  const auto &found = from_stack_alloc.find(target);
  if(found != from_stack_alloc.end())
  {
    log.warning() << "Ignored duplicate stack-allocated target '"
                  << from_expr(ns, target.id(), target) << "' at "
                  << target.source_location().as_string() << messaget::eom;
    return found->second;
  }
  else
  {
    from_stack_alloc.insert({target, create_car_expr(true_exprt{}, target)});
    return from_stack_alloc.find(target)->second;
  }
}

const car_exprt &
instrument_spec_assignst::create_car_from_heap_alloc(const exprt &target)
{
  const auto &found = from_heap_alloc.find(target);
  if(found != from_heap_alloc.end())
  {
    log.warning() << "Ignored duplicate heap-allocated target '"
                  << from_expr(ns, target.id(), target) << "' at "
                  << target.source_location().as_string() << messaget::eom;
    return found->second;
  }
  else
  {
    from_heap_alloc.insert({target, create_car_expr(true_exprt{}, target)});
    return from_heap_alloc.find(target)->second;
  }
}

void instrument_spec_assignst::invalidate_car(
  const car_exprt &tracked_car,
  const car_exprt &freed_car,
  goto_programt &result) const
{
  source_locationt source_location(freed_car.source_location());
  add_pragma_disable_pointer_checks(source_location);
  add_pragma_disable_assigns_check(source_location);

  result.add(goto_programt::make_assignment(
    tracked_car.valid_var(),
    and_exprt{tracked_car.valid_var(),
              not_exprt{same_object(
                tracked_car.lower_bound_var(), freed_car.lower_bound_var())}},
    source_location));
}

void instrument_spec_assignst::invalidate_heap_and_spec_aliases(
  const car_exprt &freed_car,
  goto_programt &dest) const
{
  for(const auto &pair : from_spec_assigns)
    invalidate_car(pair.second, freed_car, dest);

  for(const auto &pair : from_heap_alloc)
    invalidate_car(pair.second, freed_car, dest);
}
