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

/// a local pragma used to keep track and skip already instrumented instructions
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
  create_snapshot(create_car_from_heap_alloc(expr), dest);
}

void instrument_spec_assignst::check_inclusion_assignment(
  const exprt &lhs,
  optionalt<cfg_infot> &cfg_info_opt,
  goto_programt &dest) const
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

void instrument_spec_assignst::instrument_instructions(
  goto_programt &body,
  goto_programt::targett instruction_it,
  const goto_programt::targett &instruction_end,
  skip_function_paramst skip_function_params,
  optionalt<cfg_infot> &cfg_info_opt)
{
  while(instruction_it != instruction_end)
  {
    // Skip instructions marked as disabled for assigns clause checking
    if(has_disable_assigns_check_pragma(instruction_it))
    {
      instruction_it++;
      if(cfg_info_opt.has_value())
        cfg_info_opt.value().step();
      continue;
    }

    // Do not instrument this instruction again in the future,
    // since we are going to instrument it now below.
    add_pragma_disable_assigns_check(*instruction_it);

    if(
      instruction_it->is_decl() &&
      must_track_decl(instruction_it, cfg_info_opt))
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
    else if(
      instruction_it->is_assign() &&
      must_check_assign(instruction_it, skip_function_params, cfg_info_opt))
    {
      instrument_assign_statement(instruction_it, body, cfg_info_opt);
    }
    else if(instruction_it->is_function_call())
    {
      instrument_call_statement(instruction_it, body, cfg_info_opt);
    }
    else if(
      instruction_it->is_dead() &&
      must_track_dead(instruction_it, cfg_info_opt))
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
      check_inclusion_assignment(havoc_object, cfg_info_opt, payload);
      insert_before_swap_and_advance(body, instruction_it, payload);
    }

    // Move to the next instruction
    instruction_it++;
    if(cfg_info_opt.has_value())
      cfg_info_opt.value().step();
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

/// Returns true iff an `ASSIGN lhs := rhs` instruction must be instrumented.
bool instrument_spec_assignst::must_check_assign(
  const goto_programt::const_targett &target,
  skip_function_paramst skip_function_params,
  const optionalt<cfg_infot> cfg_info_opt)
{
  if(
    const auto &symbol_expr =
      expr_try_dynamic_cast<symbol_exprt>(target->assign_lhs()))
  {
    if(
      skip_function_params == skip_function_paramst::NO &&
      ns.lookup(symbol_expr->get_identifier()).is_parameter)
    {
      return true;
    }

    if(cfg_info_opt.has_value())
      return !cfg_info_opt.value().is_local(symbol_expr->get_identifier());
  }

  return true;
}

/// Returns true iff a `DECL x` must be added to the local write set.
///
/// A variable is called 'dirty' if its address gets taken at some point in
/// the program.
///
/// Assuming the goto program is obtained from a structured C program that
/// passed C compiler checks, non-dirty variables can only be assigned to
/// directly by name, cannot escape their lexical scope, and are always safe
/// to assign. Hence, we only track dirty variables in the write set.
bool instrument_spec_assignst::must_track_decl(
  const goto_programt::const_targett &target,
  const optionalt<cfg_infot> &cfg_info_opt) const
{
  if(cfg_info_opt.has_value())
  {
    return cfg_info_opt.value().is_not_local_or_dirty_local(
      target->decl_symbol().get_identifier());
  }
  // Unless proved non-dirty by the CFG analysis we assume it is dirty.
  return true;
}

/// Returns true iff a `DEAD x` must be processed to upate the local write set.
/// The conditions are the same than for tracking a `DECL x` instruction.
bool instrument_spec_assignst::must_track_dead(
  const goto_programt::const_targett &target,
  const optionalt<cfg_infot> &cfg_info_opt) const
{
  // Unless proved non-dirty by the CFG analysis we assume it is dirty.
  if(!cfg_info_opt.has_value())
    return true;

  return cfg_info_opt.value().is_not_local_or_dirty_local(
    target->dead_symbol().get_identifier());
}

void instrument_spec_assignst::instrument_assign_statement(
  goto_programt::targett &instruction_it,
  goto_programt &program,
  optionalt<cfg_infot> &cfg_info_opt) const
{
  auto lhs = instruction_it->assign_lhs();
  lhs.add_source_location() = instruction_it->source_location();
  goto_programt payload;
  check_inclusion_assignment(lhs, cfg_info_opt, payload);
  insert_before_swap_and_advance(program, instruction_it, payload);
}

void instrument_spec_assignst::instrument_call_statement(
  goto_programt::targett &instruction_it,
  goto_programt &body,
  optionalt<cfg_infot> &cfg_info_opt)
{
  PRECONDITION_WITH_DIAGNOSTICS(
    instruction_it->is_function_call(),
    "The first argument of instrument_call_statement should always be "
    "a function call");

  const auto &callee_name =
    to_symbol_expr(instruction_it->call_function()).get_identifier();

  if(callee_name == "malloc")
  {
    const auto &function_call =
      to_code_function_call(instruction_it->get_code());
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
    check_inclusion_heap_allocated_and_invalidate_aliases(
      object, cfg_info_opt, payload);
    insert_before_swap_and_advance(body, instruction_it, payload);
  }
}
