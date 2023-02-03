/*******************************************************************\

Module: Instrument assigns clauses in code contracts.

Author: Remi Delmas

Date: January 2022

\*******************************************************************/

/// \file
/// Specify write set in code contracts

#include "instrument_spec_assigns.h"

#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/format_expr.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>

#include <ansi-c/c_expr.h>
#include <langapi/language_util.h>

#include "cfg_info.h"
#include "utils.h"

/// header for log messages
static const char LOG_HEADER[] = "assigns clause checking: ";

/// Pragma used to mark assignments to static locals that need to be propagated
static const char PROPAGATE_STATIC_LOCAL_PRAGMA[] =
  "contracts:propagate-static-local";

bool has_propagate_static_local_pragma(const source_locationt &source_location)
{
  const auto &pragmas = source_location.get_pragmas();
  return pragmas.find(PROPAGATE_STATIC_LOCAL_PRAGMA) != pragmas.end();
}

void add_propagate_static_local_pragma(source_locationt &source_location)
{
  source_location.add_pragma(PROPAGATE_STATIC_LOCAL_PRAGMA);
}

/// A local pragma used to keep track and skip already instrumented instructions
const char CONTRACT_PRAGMA_DISABLE_ASSIGNS_CHECK[] =
  "contracts:disable:assigns-check";

void add_pragma_disable_pointer_checks(source_locationt &location)
{
  location.add_pragma("disable:pointer-check");
  location.add_pragma("disable:pointer-primitive-check");
  location.add_pragma("disable:pointer-overflow-check");
  location.add_pragma("disable:signed-overflow-check");
  location.add_pragma("disable:unsigned-overflow-check");
  location.add_pragma("disable:conversion-check");
}

/// Returns true iff the target instruction is tagged with a
/// 'CONTRACT_PRAGMA_DISABLE_ASSIGNS_CHECK' pragma.
bool has_disable_assigns_check_pragma(
  const goto_programt::const_targett &target)
{
  const auto &pragmas = target->source_location().get_pragmas();
  return pragmas.find(CONTRACT_PRAGMA_DISABLE_ASSIGNS_CHECK) != pragmas.end();
}

void add_pragma_disable_assigns_check(source_locationt &location)
{
  location.add_pragma(CONTRACT_PRAGMA_DISABLE_ASSIGNS_CHECK);
}

goto_programt::instructiont &
add_pragma_disable_assigns_check(goto_programt::instructiont &instr)
{
  add_pragma_disable_assigns_check(instr.source_location_nonconst());
  return instr;
}

goto_programt &add_pragma_disable_assigns_check(goto_programt &prog)
{
  Forall_goto_program_instructions(it, prog)
    add_pragma_disable_assigns_check(*it);
  return prog;
}

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
  // insert in tracking set
  const auto &car = create_car_from_heap_alloc(expr);

  // generate target validity check for this target.
  target_validity_assertion(car, true, dest);

  // generate snapshot instructions for this target.
  create_snapshot(car, dest);
}

void instrument_spec_assignst::check_inclusion_assignment(
  const exprt &lhs,
  goto_programt &dest) const
{
  // create temporary car but do not track
  const auto car = create_car_expr(true_exprt{}, lhs);
  create_snapshot(car, dest);
  inclusion_check_assertion(car, false, true, false, dest);
}

void instrument_spec_assignst::check_inclusion_induction(
  const exprt &lhs,
  goto_programt &dest) const
{
  // create temporary car but do not track
  const auto car = create_car_expr(true_exprt{}, lhs);
  create_snapshot(car, dest);
  inclusion_check_assertion(car, false, true, true, dest);
}

void instrument_spec_assignst::track_static_locals(goto_programt &dest)
{
  const auto &found = functions.function_map.find(function_id);
  INVARIANT(
    found != functions.function_map.end(),
    "the instrumented function must exist in the model");
  const goto_programt &body = found->second.body;

  propagated_static_localst propagated;
  covered_locationst covered_locations;
  covered_locations[function_id].anywhere();
  traverse_instructions(
    function_id,
    body.instructions.begin(),
    body.instructions.end(),
    covered_locations,
    propagated);

  std::unordered_set<symbol_exprt, irep_hash> symbols;
  collect_static_symbols(covered_locations, symbols);

  for(const auto &expr : propagated)
    create_snapshot(create_car_from_static_local(expr), dest);

  for(const auto &sym : symbols)
    create_snapshot(create_car_from_static_local(sym), dest);
}

void instrument_spec_assignst::track_static_locals_between(
  goto_programt::const_targett it,
  const goto_programt::const_targett end,
  goto_programt &dest)
{
  propagated_static_localst propagated;
  covered_locationst covered_locations;
  traverse_instructions(function_id, it, end, covered_locations, propagated);

  std::unordered_set<symbol_exprt, irep_hash> symbols;
  collect_static_symbols(covered_locations, symbols);

  for(const auto &sym : symbols)
    create_snapshot(create_car_from_static_local(sym), dest);

  for(const auto &expr : propagated)
    create_snapshot(create_car_from_static_local(expr), dest);
}

void instrument_spec_assignst::traverse_instructions(
  const irep_idt ambient_function_id,
  goto_programt::const_targett it,
  const goto_programt::const_targett end,
  covered_locationst &covered_locations,
  propagated_static_localst &propagated) const
{
  for(; it != end; it++)
  {
    const auto &loc = it->source_location();
    const auto &loc_fun = loc.get_function();
    if(!loc_fun.empty())
    {
      auto &itv = covered_locations[loc_fun];
      if(loc_fun == ambient_function_id)
      {
        itv.update(loc);
      }
      else
      {
        // we are on an instruction coming from some other function that the
        // ambient function so we assume that the whole function was inlined
        itv.anywhere();
      }
    }
    else
    {
      log.debug() << "Ignoring instruction without function attribute"
                  << messaget::eom;
      // ignore instructions with a source_location that
      // have no function attribute
    }

    // Collect assignments marked as "propagate static local"
    // (these are generated by havoc_assigns_clause_targett)
    if(has_propagate_static_local_pragma(loc))
    {
      INVARIANT(
        it->is_assign() && can_cast_expr<symbol_exprt>(it->assign_lhs()) &&
          can_cast_expr<side_effect_expr_nondett>(it->assign_rhs()),
        "Expected an assignment of the form `symbol_exprt := "
        "side_effect_expr_nondett`");
      // must be a nondet assignment to a symbol
      propagated.insert(to_symbol_expr(it->assign_lhs()));
    }

    // recurse into bodies of called functions if available
    if(it->is_function_call())
    {
      const auto &fun_expr = it->call_function();

      PRECONDITION_WITH_DIAGNOSTICS(
        fun_expr.id() == ID_symbol,
        "Local static search requires function pointer removal");
      const irep_idt &fun_id = to_symbol_expr(fun_expr).get_identifier();

      const auto &found = functions.function_map.find(fun_id);
      INVARIANT(
        found != functions.function_map.end(),
        "Function " + id2string(fun_id) + "not in function map");

      // do not recurse if the function was already seen before
      if(covered_locations.find(fun_id) == covered_locations.end())
      {
        // consider all locations of this function covered
        covered_locations[fun_id].anywhere();
        const goto_programt &body = found->second.body;
        if(!body.empty())
        {
          traverse_instructions(
            fun_id,
            body.instructions.begin(),
            body.instructions.end(),
            covered_locations,
            propagated);
        }
      }
    }
  }
}

void instrument_spec_assignst::collect_static_symbols(
  covered_locationst &covered_locations,
  std::unordered_set<symbol_exprt, irep_hash> &dest)
{
  for(const auto &sym_pair : st)
  {
    const auto &sym = sym_pair.second;
    if(sym.is_static_lifetime)
    {
      const auto &loc = sym.location;
      if(!loc.get_function().empty())
      {
        const auto &itv = covered_locations.find(loc.get_function());
        if(itv != covered_locations.end() && itv->second.contains(sym.location))
          dest.insert(sym.symbol_expr());
      }
    }
  }
}

void instrument_spec_assignst::
  check_inclusion_heap_allocated_and_invalidate_aliases(
    const exprt &expr,

    goto_programt &dest)
{
  // create temporary car but do not track
  const auto car = create_car_expr(true_exprt{}, expr);

  // generate snapshot instructions for this target.
  create_snapshot(car, dest);

  // check inclusion, allowing null and not allowing stack allocated locals
  inclusion_check_assertion(car, true, false, false, dest);

  // invalidate aliases of the freed object
  invalidate_heap_and_spec_aliases(car, dest);
}

void instrument_spec_assignst::instrument_instructions(
  goto_programt &body,
  goto_programt::targett instruction_it,
  const goto_programt::targett &instruction_end,
  const std::function<bool(const goto_programt::targett &)> &pred)
{
  while(instruction_it != instruction_end)
  {
    // Skip instructions marked as disabled for assigns clause checking
    if(
      has_disable_assigns_check_pragma(instruction_it) ||
      (pred && !pred(instruction_it)))
    {
      instruction_it++;
      continue;
    }

    // Do not instrument this instruction again in the future,
    // since we are going to instrument it now below.
    add_pragma_disable_assigns_check(*instruction_it);

    if(instruction_it->is_decl() && must_track_decl(instruction_it))
    {
      // grab the declared symbol
      const auto &decl_symbol = instruction_it->decl_symbol();
      // move past the call and then insert the CAR
      instruction_it++;
      goto_programt payload;
      track_stack_allocated(decl_symbol, payload);
      insert_before_swap_and_advance(body, instruction_it, payload);
      // since CAR was inserted *after* the DECL instruction,
      // move the instruction pointer backward,
      // because the enclosing while loop step takes
      // care of the increment
      instruction_it--;
    }
    else if(instruction_it->is_assign() && must_check_assign(instruction_it))
    {
      instrument_assign_statement(instruction_it, body);
    }
    else if(instruction_it->is_function_call())
    {
      instrument_call_statement(instruction_it, body);
    }
    else if(instruction_it->is_dead() && must_track_dead(instruction_it))
    {
      const auto &symbol = instruction_it->dead_symbol();
      if(stack_allocated_is_tracked(symbol))
      {
        goto_programt payload;
        invalidate_stack_allocated(symbol, payload);
        insert_before_swap_and_advance(body, instruction_it, payload);
      }
      else
      {
        // Some variables declared outside of the loop
        // can go `DEAD` (possible conditionally) when return
        // statements exist inside the loop body.
        // Since they are not DECL'd inside the loop, these locations
        // are not automatically tracked in the stack_allocated map,
        // so to be writable these variables must be listed in the assigns
        // clause.
        log.warning() << "Found a `DEAD` variable " << symbol.get_identifier()
                      << " without corresponding `DECL`, at: "
                      << instruction_it->source_location() << messaget::eom;
      }
    }
    else if(
      instruction_it->is_other() &&
      instruction_it->get_other().get_statement() == ID_havoc_object)
    {
      auto havoc_argument = instruction_it->get_other().operands().front();
      auto havoc_object = pointer_object(havoc_argument);
      havoc_object.add_source_location() = instruction_it->source_location();
      goto_programt payload;
      check_inclusion_assignment(havoc_object, payload);
      insert_before_swap_and_advance(body, instruction_it, payload);
    }

    // Move to the next instruction
    instruction_it++;
  }
}

void instrument_spec_assignst::track_spec_target_group(
  const conditional_target_group_exprt &group,
  goto_programt &dest)
{
  // clean up side effects from the guard expression if needed
  cleanert cleaner(st, log.get_message_handler());
  exprt condition(group.condition());
  if(has_subexpr(condition, ID_side_effect))
    cleaner.clean(condition, dest, mode);

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
  return new_tmp_symbol(type, location, mode, st, suffix);
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
    const auto &arg = to_pointer_object_expr(target).pointer();
    return {
      condition,
      target,
      minus_exprt(
        typecast_exprt::conditional_cast(arg, pointer_type(char_type())),
        pointer_offset(arg)),
      typecast_exprt::conditional_cast(object_size(arg), size_type()),
      valid_var,
      lower_bound_var,
      upper_bound_var,
      car_havoc_methodt::HAVOC_OBJECT};
  }
  else if(can_cast_expr<side_effect_expr_function_callt>(target))
  {
    const auto &funcall = to_side_effect_expr_function_call(target);
    if(can_cast_expr<symbol_exprt>(funcall.function()))
    {
      const auto &ident = to_symbol_expr(funcall.function()).get_identifier();

      PRECONDITION_WITH_DIAGNOSTICS(
        ident == CPROVER_PREFIX "object_from" ||
          ident == CPROVER_PREFIX "object_upto" ||
          ident == CPROVER_PREFIX "object_whole" ||
          ident == CPROVER_PREFIX "assignable",
        "call to function '" + id2string(ident) +
          "' in assigns clause not supported yet");

      if(ident == CPROVER_PREFIX "object_from")
      {
        const auto &ptr = funcall.arguments().at(0);
        return {
          condition,
          target,
          // lb = ptr
          typecast_exprt::conditional_cast(ptr, pointer_type(char_type())),
          // size = object_size(ptr) - pointer_offset(ptr)
          typecast_exprt::conditional_cast(
            minus_exprt{
              typecast_exprt::conditional_cast(
                object_size(ptr), signed_size_type()),
              pointer_offset(ptr)},
            size_type()),
          valid_var,
          lower_bound_var,
          upper_bound_var,
          car_havoc_methodt::HAVOC_SLICE};
      }
      else if(ident == CPROVER_PREFIX "object_upto")
      {
        const auto &ptr = funcall.arguments().at(0);
        const auto &size = funcall.arguments().at(1);
        return {
          condition,
          target,
          // lb = ptr
          typecast_exprt::conditional_cast(ptr, pointer_type(char_type())),
          // size = size
          typecast_exprt::conditional_cast(size, size_type()),
          valid_var,
          lower_bound_var,
          upper_bound_var,
          car_havoc_methodt::HAVOC_SLICE};
      }
      else if(ident == CPROVER_PREFIX "object_whole")
      {
        const auto &ptr = funcall.arguments().at(0);
        return {
          condition,
          target,
          // lb = ptr - pointer_offset(ptr)
          minus_exprt(
            typecast_exprt::conditional_cast(ptr, pointer_type(char_type())),
            pointer_offset(ptr)),
          // size = object_size(ptr)
          typecast_exprt::conditional_cast(object_size(ptr), size_type()),
          valid_var,
          lower_bound_var,
          upper_bound_var,
          car_havoc_methodt::HAVOC_OBJECT};
      }
      else if(ident == CPROVER_PREFIX "assignable")
      {
        const auto &ptr = funcall.arguments().at(0);
        const auto &size = funcall.arguments().at(1);
        const auto &is_ptr_to_ptr = funcall.arguments().at(2);
        return {
          condition,
          target,
          // lb = ptr
          typecast_exprt::conditional_cast(ptr, pointer_type(char_type())),
          // size = size
          typecast_exprt::conditional_cast(size, size_type()),
          valid_var,
          lower_bound_var,
          upper_bound_var,
          is_ptr_to_ptr.is_true() ? car_havoc_methodt::NONDET_ASSIGN
                                  : car_havoc_methodt::HAVOC_SLICE};
      }
    }
  }
  else if(is_assignable(target))
  {
    const auto &size = size_of_expr(target.type(), ns);

    INVARIANT(
      size.has_value(),
      "no definite size for lvalue target:\n" + target.pretty());

    return {
      condition,
      target,
      // lb = &target
      typecast_exprt::conditional_cast(
        address_of_exprt{target}, pointer_type(char_type())),
      // size = sizeof(target)
      typecast_exprt::conditional_cast(size.value(), size_type()),
      valid_var,
      lower_bound_var,
      upper_bound_var,
      car_havoc_methodt::NONDET_ASSIGN};
  }

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
      and_exprt{
        car.condition(), not_exprt{null_object(car.target_start_address())}},
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
  // not of the right size (or is NULL if we do not allow it explicitly).
  auto result =
    or_exprt{not_exprt{car.condition()},
             w_ok_exprt{car.target_start_address(), car.target_size()}};

  if(allow_null_target)
    result.add_to_operands(null_object(car.target_start_address()));

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
  bool is_inductive_check,
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

  if(is_inductive_check)
    comment += " is inductively assignable";
  else
    comment += " is assignable";
  source_location.set_comment(comment);

  exprt inclusion_check =
    inclusion_check_full(car, allow_null_lhs, include_stack_allocated);
  // Record what target is checked.
  auto &checked_assigns =
    static_cast<exprt &>(inclusion_check.add(ID_checked_assigns));
  checked_assigns = car.target();

  dest.add(goto_programt::make_assertion(inclusion_check, source_location));
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
  bool include_stack_allocated) const
{
  bool no_targets = from_spec_assigns.empty() && from_heap_alloc.empty() &&
                    (!include_stack_allocated ||
                     (from_static_local.empty() && from_stack_alloc.empty()));

  // inclusion check expression
  if(no_targets)
  {
    // if null lhs are allowed then we should have a null lhs when
    // we reach this program point, otherwise we should never reach
    // this program point
    if(allow_null_lhs)
      return null_object(car.target_start_address());
    else
      return false_exprt{};
  }

  // Build a disjunction over all tracked locations
  exprt::operandst disjuncts;
  log.debug() << LOG_HEADER << " inclusion check: \n"
              << from_expr_using_mode(ns, mode, car.target()) << " in {"
              << messaget::eom;

  for(const auto &pair : from_spec_assigns)
  {
    disjuncts.push_back(inclusion_check_single(car, pair.second));
    log.debug() << "\t(spec) "
                << from_expr_using_mode(ns, mode, pair.second.target())
                << messaget::eom;
  }

  for(const auto &heap_car : from_heap_alloc)
  {
    disjuncts.push_back(inclusion_check_single(car, heap_car));
    log.debug() << "\t(heap) "
                << from_expr_using_mode(ns, mode, heap_car.target())
                << messaget::eom;
  }

  if(include_stack_allocated)
  {
    for(const auto &pair : from_stack_alloc)
    {
      disjuncts.push_back(inclusion_check_single(car, pair.second));
      log.debug() << "\t(stack) "
                  << from_expr_using_mode(ns, mode, pair.second.target())
                  << messaget::eom;
    }

    // static locals are stack allocated and can never be DEAD
    for(const auto &pair : from_static_local)
    {
      disjuncts.push_back(inclusion_check_single(car, pair.second));
      log.debug() << "\t(static) "
                  << from_expr_using_mode(ns, mode, pair.second.target())
                  << messaget::eom;
    }
  }
  log.debug() << "}" << messaget::eom;

  if(allow_null_lhs)
    return or_exprt{
      null_object(car.target_start_address()),
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
    log.debug() << LOG_HEADER << "creating CAR for assigns clause target "
                << format(condition) << ": " << format(target) << messaget::eom;
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
    log.debug() << LOG_HEADER << "creating CAR for stack-allocated target "
                << format(target) << messaget::eom;
    from_stack_alloc.insert({target, create_car_expr(true_exprt{}, target)});
    return from_stack_alloc.find(target)->second;
  }
}

const car_exprt &
instrument_spec_assignst::create_car_from_heap_alloc(const exprt &target)
{
  log.debug() << LOG_HEADER << "creating CAR for heap-allocated target "
              << format(target) << messaget::eom;
  from_heap_alloc.emplace_back(create_car_expr(true_exprt{}, target));
  return from_heap_alloc.back();
}

const car_exprt &instrument_spec_assignst::create_car_from_static_local(
  const symbol_exprt &target)
{
  const auto &found = from_static_local.find(target);
  if(found != from_static_local.end())
  {
    log.warning() << "Ignored duplicate static local var target '"
                  << from_expr(ns, target.id(), target) << "' at "
                  << target.source_location().as_string() << messaget::eom;
    return found->second;
  }
  else
  {
    log.debug() << LOG_HEADER << "creating CAR for static local target "
                << format(target) << messaget::eom;
    from_static_local.insert({target, create_car_expr(true_exprt{}, target)});
    return from_static_local.find(target)->second;
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

  for(const auto &car : from_heap_alloc)
    invalidate_car(car, freed_car, dest);
}

/// Returns true iff an `ASSIGN lhs := rhs` instruction must be instrumented.
bool instrument_spec_assignst::must_check_assign(
  const goto_programt::const_targett &target)
{
  log.debug().source_location = target->source_location();

  if(can_cast_expr<symbol_exprt>(target->assign_lhs()))
  {
    const auto &symbol_expr = to_symbol_expr(target->assign_lhs());

    if(cfg_info.is_local(symbol_expr.get_identifier()))
    {
      log.debug() << LOG_HEADER
                  << "skipping checking on assignment to local symbol "
                  << format(symbol_expr) << messaget::eom;
      return false;
    }
    else
    {
      log.debug() << LOG_HEADER << "checking assignment to non-local symbol "
                  << format(symbol_expr) << messaget::eom;
      return true;
    }

    log.debug() << LOG_HEADER << "checking assignment to symbol "
                << format(symbol_expr) << messaget::eom;
    return true;
  }
  else
  {
    // This is not a mere symbol.
    // Since non-dirty locals are not tracked explicitly in the write set,
    // we need to skip the check if we can verify that the expression describes
    // an access to a non-dirty local symbol or an input parameter,
    // otherwise the check will fail.
    // In addition, the expression shall not contain address_of or dereference
    // operators, regardless of the base symbol/object on which they apply.
    // If the expression contains an address_of operation, the assignment gets
    // checked. If the base object is a local or a parameter, it will also be
    // flagged as dirty and will be tracked explicitly, and the check will pass.
    // If the expression contains a dereference operation, the assignment gets
    // checked. If the dereferenced address was computed from a local object,
    // from a function parameter or returned by a local malloc,
    // then the object will be tracked explicitly and the check will pass.
    // In all other cases (address of a non-local object, or dereference of
    // a non-locally computed address) the location must be given explicitly
    // in the assigns clause to be tracked and we must check the assignment.
    if(cfg_info.is_local_composite_access(target->assign_lhs()))
    {
      log.debug()
        << LOG_HEADER
        << "skipping check on assignment to local composite member expression "
        << format(target->assign_lhs()) << messaget::eom;
      return false;
    }
    log.debug() << LOG_HEADER << "checking assignment to expression "
                << format(target->assign_lhs()) << messaget::eom;
    return true;
  }
}

/// Track the symbol is not a local or is a dirty local.
bool instrument_spec_assignst::must_track_decl_or_dead(
  const irep_idt &ident) const
{
  return cfg_info.is_not_local_or_dirty_local(ident);
}

/// Returns true iff a `DECL x` must be explicitly tracked in the write set.
bool instrument_spec_assignst::must_track_decl(
  const goto_programt::const_targett &target) const
{
  log.debug().source_location = target->source_location();
  if(must_track_decl_or_dead(target->decl_symbol().get_identifier()))
  {
    log.debug() << LOG_HEADER << "explicitly tracking "
                << format(target->decl_symbol()) << " as assignable"
                << messaget::eom;
    return true;
  }
  else
  {
    log.debug() << LOG_HEADER << "implicitly tracking "
                << format(target->decl_symbol())
                << " as assignable (non-dirty local)" << messaget::eom;
    return false;
  }
}

/// Returns true iff a `DEAD x` must be processed to upate the local write set.
/// The conditions are the same than for tracking a `DECL x` instruction.
bool instrument_spec_assignst::must_track_dead(
  const goto_programt::const_targett &target) const
{
  return must_track_decl_or_dead(target->dead_symbol().get_identifier());
}

void instrument_spec_assignst::instrument_assign_statement(
  goto_programt::targett &instruction_it,
  goto_programt &program) const
{
  auto lhs = instruction_it->assign_lhs();
  lhs.add_source_location() = instruction_it->source_location();
  goto_programt payload;
  check_inclusion_assignment(lhs, payload);
  insert_before_swap_and_advance(program, instruction_it, payload);
}

void instrument_spec_assignst::instrument_call_statement(
  goto_programt::targett &instruction_it,
  goto_programt &body)
{
  PRECONDITION_WITH_DIAGNOSTICS(
    instruction_it->is_function_call(),
    "The first argument of instrument_call_statement should always be "
    "a function call");

  const auto &callee_name =
    to_symbol_expr(instruction_it->call_function()).get_identifier();

  if(callee_name == "malloc")
  {
    const auto &function_call = to_code_function_call(instruction_it->code());
    if(function_call.lhs().is_not_nil())
    {
      // grab the returned pointer from malloc
      auto object = pointer_object(function_call.lhs());
      object.add_source_location() = function_call.source_location();
      // move past the call and then insert the CAR
      instruction_it++;
      goto_programt payload;
      track_heap_allocated(object, payload);
      insert_before_swap_and_advance(body, instruction_it, payload);
      // since CAR was inserted *after* the malloc call,
      // move the instruction pointer backward,
      // because the caller increments it in a `for` loop
      instruction_it--;
    }
  }
  else if(callee_name == "free")
  {
    const auto &ptr = instruction_it->call_arguments().front();
    auto object = pointer_object(ptr);
    object.add_source_location() = instruction_it->source_location();
    goto_programt payload;
    check_inclusion_heap_allocated_and_invalidate_aliases(object, payload);
    insert_before_swap_and_advance(body, instruction_it, payload);
  }
}
