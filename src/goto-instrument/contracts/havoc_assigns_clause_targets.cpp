/*******************************************************************\

Module: Havoc multiple and possibly dependent targets simultaneously

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

/// \file
/// Havoc multiple and possibly dependent targets simultaneously

#include "havoc_assigns_clause_targets.h"

#include <util/c_types.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>

#include "instrument_spec_assigns.h"
#include "utils.h"

void havoc_assigns_clause_targetst::get_instructions(goto_programt &dest)
{
  // snapshotting instructions and well-definedness checks
  goto_programt snapshot_program;

  // add static locals called touched by the replaced function
  track_static_locals(snapshot_program);

  // add spec targets
  for(const auto &target : targets)
    track_spec_target(target, snapshot_program);

  // generate havocking instructions for all tracked CARs
  goto_programt havoc_program;
  for(const auto &pair : from_spec_assigns)
    havoc_if_valid(pair.second, havoc_program);

  for(const auto &pair : from_stack_alloc)
    havoc_if_valid(pair.second, havoc_program);

  for(const auto &car : from_heap_alloc)
    havoc_if_valid(car, havoc_program);

  for(const auto &pair : from_static_local)
  {
    havoc_static_local(pair.second, havoc_program);
  }

  // append to dest
  dest.destructive_append(snapshot_program);
  dest.destructive_append(havoc_program);
}

void havoc_assigns_clause_targetst::havoc_if_valid(
  car_exprt car,
  goto_programt &dest)
{
  const irep_idt &tracking_comment =
    make_assigns_clause_replacement_tracking_comment(
      car.target(), function_id, ns);

  source_locationt source_location_no_checks(source_location);
  add_pragma_disable_pointer_checks(source_location_no_checks);

  goto_programt skip_program;
  const auto skip_target =
    skip_program.add(goto_programt::make_skip(source_location_no_checks));

  dest.add(goto_programt::make_goto(
    skip_target, not_exprt{car.valid_var()}, source_location_no_checks));

  if(car.havoc_method == car_havoc_methodt::HAVOC_OBJECT)
  {
    // OTHER __CPROVER_havoc_object(target_snapshot_var)
    codet code(ID_havoc_object, {car.lower_bound_var()});
    source_locationt annotated_location = source_location;
    annotated_location.set_comment(tracking_comment);
    dest.add(goto_programt::make_other(code, annotated_location));
  }
  else if(car.havoc_method == car_havoc_methodt::HAVOC_SLICE)
  {
    // This is a slice target. We use goto convert's do_havoc_slice()
    // code generation, provided by cleanert.
    cleanert cleaner(st, log.get_message_handler());
    const auto &mode = st.lookup_ref(function_id).mode;
    const auto &funcall = to_side_effect_expr_function_call(car.target());
    const auto &function = to_symbol_expr(funcall.function());
    exprt::operandst arguments;
    arguments.push_back(car.lower_bound_var());
    arguments.push_back(car.target_size());
    cleaner.do_havoc_slice(function, arguments, dest, mode);
  }
  else if(car.havoc_method == car_havoc_methodt::NONDET_ASSIGN)
  {
    // a target where the size is derived from the type of the target
    // ASSIGN *(target.type() *)__car_lb = nondet(car.target().type())
    const auto &target_type = car.target().type();
    side_effect_expr_nondett nondet(target_type, source_location);
    source_locationt annotated_location = source_location;
    annotated_location.set_comment(tracking_comment);
    dest.add(goto_programt::make_assignment(
      dereference_exprt{typecast_exprt::conditional_cast(
        car.lower_bound_var(), pointer_type(target_type))},
      nondet,
      annotated_location));
  }
  else
  {
    UNREACHABLE;
  }

  dest.destructive_append(skip_program);

  dest.add(
    goto_programt::make_dead(car.valid_var(), source_location_no_checks));

  dest.add(
    goto_programt::make_dead(car.lower_bound_var(), source_location_no_checks));

  dest.add(
    goto_programt::make_dead(car.upper_bound_var(), source_location_no_checks));
}

void havoc_assigns_clause_targetst::havoc_static_local(
  car_exprt car,
  goto_programt &dest)
{
  // We havoc the target expression directly for local statics
  // instead of the __car_lb pointer because we know statics never die
  // and cannot be involved in in dependencies
  // since we cannot talk about them in contracts.
  const irep_idt &tracking_comment =
    make_assigns_clause_replacement_tracking_comment(
      car.target(), function_id, ns);

  source_locationt source_location_no_checks(source_location);
  add_pragma_disable_pointer_checks(source_location_no_checks);

  goto_programt skip_program;
  const auto skip_target =
    skip_program.add(goto_programt::make_skip(source_location_no_checks));

  dest.add(goto_programt::make_goto(
    skip_target, not_exprt{car.valid_var()}, source_location_no_checks));

  const auto &target_type = car.target().type();
  side_effect_expr_nondett nondet(target_type, source_location);
  source_locationt annotated_location = source_location;
  annotated_location.set_comment(tracking_comment);
  add_propagate_static_local_pragma(annotated_location);
  dest.add(
    goto_programt::make_assignment(car.target(), nondet, annotated_location));

  dest.destructive_append(skip_program);

  dest.add(
    goto_programt::make_dead(car.valid_var(), source_location_no_checks));

  dest.add(
    goto_programt::make_dead(car.lower_bound_var(), source_location_no_checks));

  dest.add(
    goto_programt::make_dead(car.upper_bound_var(), source_location_no_checks));
}
