/*******************************************************************\

Module: Havoc multiple and possibly dependent targets simultaneously

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

/// \file
/// Havoc multiple and possibly dependent targets simultaneously

#include "havoc_assigns_clause_targets.h"

#include <map>

#include <langapi/language_util.h>

#include <util/c_types.h>
#include <util/format_expr.h>
#include <util/format_type.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/std_code.h>

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

/// Returns a pointer expression to the start address of the target
///
/// - If the target is a `pointer_object(p)` expression,
///   return a pointer to the same object with offset zero
/// - else, if the target is a sized and assignable expression,
///   return its address
/// - else trigger an error.
///
static exprt build_address_of(
  const exprt &target,
  // context parameters
  const namespacet &ns)
{
  if(target.id() == ID_pointer_object)
  {
    const auto &ptr = target.operands().front();
    // bring the offset back to zero
    return minus_exprt{ptr, pointer_offset(ptr)};
  }
  else if(is_assignable(target))
  {
    INVARIANT(
      size_of_expr(target.type(), ns).has_value(),
      "`sizeof` must always be computable on assignable assigns clause "
      "targets.");

    return address_of_exprt{target};
  }
  UNREACHABLE;
}

/// \brief Generates instructions to conditionally snapshot the value
/// of `target_pointer` into `target_snapshot_var`.
///
/// ```
/// DECL target_valid_var : bool
/// DECL target_snapshot_var : <target_pointer.type()>
/// ASSIGN target_valid_var := <all_dereferences_valid(target_pointer)>
/// ASSIGN target_snapshot_var := NULL
/// IF !target_valid_var GOTO skip_target
/// ASSIGN target_snapshot_var := target_pointer;
/// skip_target: SKIP
/// ```
///
static void snapshot_if_valid(
  const symbol_exprt &target_valid_var,
  const symbol_exprt &target_snapshot_var,
  const exprt &target_pointer,
  goto_programt &dest,
  // context parameters
  const source_locationt &source_location,
  const namespacet &ns)
{
  source_locationt source_location_no_checks(source_location);
  disable_pointer_checks(source_location_no_checks);

  dest.add(goto_programt::make_decl(target_valid_var));

  dest.add(goto_programt::make_decl(target_snapshot_var));

  dest.add(goto_programt::make_assignment(
    target_valid_var,
    all_dereferences_are_valid(target_pointer, ns),
    source_location_no_checks));

  dest.add(goto_programt::make_assignment(
    target_snapshot_var,
    null_pointer_exprt{to_pointer_type(target_pointer.type())},
    source_location_no_checks));

  goto_programt skip_program;
  const auto skip_target =
    skip_program.add(goto_programt::make_skip(source_location_no_checks));

  dest.add(goto_programt::make_goto(
    skip_target, not_exprt{target_valid_var}, source_location_no_checks));

  dest.add(goto_programt::make_assignment(
    target_snapshot_var, target_pointer, source_location_no_checks));

  dest.destructive_append(skip_program);
}

/// \brief Generates instructions to conditionally havoc
/// the given `target_snapshot_var`.
///
/// Generates these instructions if target is a `__CPROVER_POINTER_OBJECT(...)`:
///
/// ```
/// IF !target_valid_var GOTO skip_target
/// OTHER havoc_object(target_snapshot_var)
/// skip_target: SKIP
/// DEAD target_valid_var
/// DEAD target_snapshot_var
/// ```
///
/// And generate these instructions otherwise:
///
/// ```
/// IF !target_valid_var GOTO skip_target
/// ASSIGN *target_snapshot_var = nondet()
/// skip_target: SKIP
/// DEAD target_valid_var
/// DEAD target_snapshot_var
/// ```
/// Adds a special comment on the havoc instructions in order to trace back
/// the havoc to the replaced function.
static void havoc_if_valid(
  const symbol_exprt &target_valid_var,
  const symbol_exprt &target_snapshot_var,
  const exprt &target,
  const irep_idt &tracking_comment,
  goto_programt &dest,
  // context parameters
  const source_locationt &source_location,
  const namespacet &ns)
{
  source_locationt source_location_no_checks(source_location);
  disable_pointer_checks(source_location_no_checks);

  goto_programt skip_program;
  const auto skip_target =
    skip_program.add(goto_programt::make_skip(source_location_no_checks));

  dest.add(goto_programt::make_goto(
    skip_target, not_exprt{target_valid_var}, source_location_no_checks));

  if(target.id() == ID_pointer_object)
  {
    // OTHER __CPROVER_havoc_object(target_snapshot_var)
    codet code(ID_havoc_object, {target_snapshot_var});
    const auto &inst =
      dest.add(goto_programt::make_other(code, source_location));
    inst->source_location_nonconst().set_comment(tracking_comment);
  }
  else
  {
    // ASSIGN *target_snapshot_var = nondet()
    side_effect_expr_nondett nondet(target.type(), source_location);
    const auto &inst = dest.add(goto_programt::make_assignment(
      dereference_exprt{target_snapshot_var}, nondet, source_location));
    inst->source_location_nonconst().set_comment(tracking_comment);
  }

  dest.destructive_append(skip_program);

  dest.add(
    goto_programt::make_dead(target_valid_var, source_location_no_checks));

  dest.add(
    goto_programt::make_dead(target_snapshot_var, source_location_no_checks));
}

void havoc_assigns_clause_targets(
  const irep_idt &replaced_function_id,
  const std::vector<exprt> &targets,
  goto_programt &dest,
  // context parameters
  const source_locationt &source_location,
  const irep_idt &mode,
  namespacet &ns,
  symbol_tablet &st)
{
  goto_programt snapshot_program;
  goto_programt havoc_program;

  for(const auto &target : targets)
  {
    const auto &tracking_comment =
      make_tracking_comment(target, replaced_function_id, ns);

    const auto target_pointer = build_address_of(target, ns);
    const auto target_snapshot_var = new_tmp_symbol(
                                       target_pointer.type(),
                                       source_location,
                                       mode,
                                       st,
                                       "__target_snapshot_var",
                                       true)
                                       .symbol_expr();
    const auto target_valid_var =
      new_tmp_symbol(
        bool_typet(), source_location, mode, st, "__target_valid_var", true)
        .symbol_expr();

    snapshot_if_valid(
      target_valid_var,
      target_snapshot_var,
      target_pointer,
      snapshot_program,
      source_location,
      ns);
    havoc_if_valid(
      target_valid_var,
      target_snapshot_var,
      target,
      tracking_comment,
      havoc_program,
      source_location,
      ns);
  }

  dest.destructive_append(snapshot_program);
  dest.destructive_append(havoc_program);
}
