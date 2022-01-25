/*******************************************************************\

Module: Havoc multiple and possibly dependent targets simultaneously

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

/// \file
/// Havoc multiple and possibly dependent targets simultaneously

#include "havoc_assigns_clause_targets.h"

#include <map>

#include <langapi/language_util.h>

#include <ansi-c/c_expr.h>

#include <util/c_types.h>
#include <util/format_expr.h>
#include <util/format_type.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/std_code.h>

#include "instrument_spec_assigns.h"
#include "utils.h"

static const char ASSIGNS_CLAUSE_REPLACEMENT_TRACKING[] =
  " (assigned by the contract of ";

static irep_idt make_tracking_comment(
  const exprt &target,
  const irep_idt &function_id,
  const namespacet &ns)
{
  return from_expr(ns, target.id(), target) +
         ASSIGNS_CLAUSE_REPLACEMENT_TRACKING + id2string(function_id) + ")";
}

bool is_assigns_clause_replacement_tracking_comment(const irep_idt &comment)
{
  return id2string(comment).find(ASSIGNS_CLAUSE_REPLACEMENT_TRACKING) !=
         std::string::npos;
}

void havoc_assigns_clause_targetst::get_instructions(goto_programt &dest)
{
  // snapshotting instructions and well-definedness checks
  goto_programt snapshot_program;

  // add spec targets
  for(const auto &target : targets)
    track_spec_target(target, snapshot_program);

  // add static locals called touched by the replaced function
  track_static_locals(snapshot_program);

  // generate havocking instructions for all tracked CARs
  goto_programt havoc_program;
  for(const auto &pair : from_spec_assigns)
    havoc_if_valid(pair.second, havoc_program);

  for(const auto &pair : from_stack_alloc)
    havoc_if_valid(pair.second, havoc_program);

  for(const auto &pair : from_heap_alloc)
    havoc_if_valid(pair.second, havoc_program);

  // append to dest
  dest.destructive_append(snapshot_program);
  dest.destructive_append(havoc_program);
}

void havoc_assigns_clause_targetst::havoc_if_valid(
  car_exprt car,
  goto_programt &dest)
{
  const irep_idt &tracking_comment =
    make_tracking_comment(car.target(), function_id, ns);

  source_locationt source_location_no_checks(source_location);
  add_pragma_disable_pointer_checks(source_location_no_checks);

  goto_programt skip_program;
  const auto skip_target =
    skip_program.add(goto_programt::make_skip(source_location_no_checks));

  dest.add(goto_programt::make_goto(
    skip_target, not_exprt{car.valid_var()}, source_location_no_checks));

  if(car.target().id() == ID_pointer_object)
  {
    // OTHER __CPROVER_havoc_object(target_snapshot_var)
    codet code(ID_havoc_object, {car.lower_bound_var()});
    const auto &inst =
      dest.add(goto_programt::make_other(code, source_location));
    inst->source_location_nonconst().set_comment(tracking_comment);
  }
  else
  {
    // ASSIGN *(target.type() *)__car_lb = nondet(car.target().type())
    const auto &target_type = car.target().type();
    side_effect_expr_nondett nondet(target_type, source_location);
    const auto &inst = dest.add(goto_programt::make_assignment(
      dereference_exprt{typecast_exprt::conditional_cast(
        car.lower_bound_var(), pointer_type(target_type))},
      nondet,
      source_location));
    inst->source_location_nonconst().set_comment(tracking_comment);
  }

  dest.destructive_append(skip_program);

  dest.add(
    goto_programt::make_dead(car.valid_var(), source_location_no_checks));

  dest.add(
    goto_programt::make_dead(car.lower_bound_var(), source_location_no_checks));

  dest.add(
    goto_programt::make_dead(car.upper_bound_var(), source_location_no_checks));
}
