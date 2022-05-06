/*******************************************************************\

Module: GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// GOTO Programs

#include "goto_check.h"

#include <util/options.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>

#include "goto_model.h"
#include "remove_skip.h"

static void transform_assertions_assumptions(
  goto_programt &goto_program,
  bool enable_assertions,
  bool enable_built_in_assertions,
  bool enable_assumptions)
{
  bool did_something = false;

  for(auto &instruction : goto_program.instructions)
  {
    if(instruction.is_assert())
    {
      bool is_user_provided =
        instruction.source_location().get_bool("user-provided");

      if(
        (is_user_provided && !enable_assertions &&
         instruction.source_location().get_property_class() != "error label") ||
        (!is_user_provided && !enable_built_in_assertions))
      {
        instruction.turn_into_skip();
        did_something = true;
      }
    }
    else if(instruction.is_assume())
    {
      if(!enable_assumptions)
      {
        instruction.turn_into_skip();
        did_something = true;
      }
    }
  }

  if(did_something)
    remove_skip(goto_program);
}

void transform_assertions_assumptions(
  const optionst &options,
  goto_modelt &goto_model)
{
  const bool enable_assertions = options.get_bool_option("assertions");
  const bool enable_built_in_assertions =
    options.get_bool_option("built-in-assertions");
  const bool enable_assumptions = options.get_bool_option("assumptions");

  // check whether there could possibly be anything to do
  if(enable_assertions && enable_built_in_assertions && enable_assumptions)
    return;

  for(auto &entry : goto_model.goto_functions.function_map)
  {
    transform_assertions_assumptions(
      entry.second.body,
      enable_assertions,
      enable_built_in_assertions,
      enable_assumptions);
  }
}

void transform_assertions_assumptions(
  const optionst &options,
  goto_programt &goto_program)
{
  const bool enable_assertions = options.get_bool_option("assertions");
  const bool enable_built_in_assertions =
    options.get_bool_option("built-in-assertions");
  const bool enable_assumptions = options.get_bool_option("assumptions");

  // check whether there could possibly be anything to do
  if(enable_assertions && enable_built_in_assertions && enable_assumptions)
    return;

  transform_assertions_assumptions(
    goto_program,
    enable_assertions,
    enable_built_in_assertions,
    enable_assumptions);
}

void remove_disabled_checks(const optionst &options, goto_modelt &goto_model)
{
  // properties to keep
  const bool enable_bounds_check = options.get_bool_option("bounds-check");
  const bool enable_conversion_check =
    options.get_bool_option("conversion-check");
  const bool enable_div_by_zero_check =
    options.get_bool_option("div-by-zero-check");
  const bool enable_enum_range_check =
    options.get_bool_option("enum-range-check");
  const bool enable_float_overflow_check =
    options.get_bool_option("float-overflow-check");
  const bool enable_memory_leak_check =
    options.get_bool_option("memory-leak-check");
  const bool enable_nan_check = options.get_bool_option("nan-check");
  const bool enable_pointer_check = options.get_bool_option("pointer-check");
  const bool enable_pointer_overflow_check =
    options.get_bool_option("pointer-overflow-check");
  const bool enable_pointer_primitive_check =
    options.get_bool_option("pointer-primitive-check");
  const bool enable_signed_overflow_check =
    options.get_bool_option("signed-overflow-check");
  const bool enable_undefined_shift_check =
    options.get_bool_option("undefined-shift-check");
  const bool enable_unsigned_overflow_check =
    options.get_bool_option("unsigned-overflow-check");
  const auto error_labels = options.get_list_option("error-label");

  // transformations retained on properties
  // const bool enable_simplify = options.get_bool_option("simplify");
  const bool enable_assert_to_assume =
    options.get_bool_option("assert-to-assume");
  // const bool retain_trivial = options.get_bool_option("retain-trivial-checks");

  const std::unordered_map<irep_idt, bool> should_skip = {
    {"NaN", !enable_nan_check},
    {"array bounds", !enable_bounds_check},
    {"bit count", !enable_bounds_check},
    {"division-by-zero", !enable_div_by_zero_check},
    {"enum-range-check", !enable_enum_range_check},
    {"error label", error_labels.empty()}, // further evaluation is necessary
    {"memory-leak", !enable_memory_leak_check},
    {"overflow", false}, // further evaluation is necessary
    {"pointer arithmetic",
     !enable_pointer_check && !enable_pointer_overflow_check},
    {"pointer dereference", !enable_pointer_check},
    {"pointer primitives", !enable_pointer_primitive_check},
    {"pointer", !enable_pointer_check},
    {"undefined-shift", !enable_undefined_shift_check}};

  const namespacet ns(goto_model.symbol_table);

  for(auto &entry : goto_model.goto_functions.function_map)
  {
    bool added_skip = false;

    for(auto &instruction : entry.second.body.instructions)
    {
      // TODO: we may have other code using __CPROVER_dead_object and therefore
      // cannot easily remove these assignments
#if 0
      if(
        instruction.is_assign() && !enable_pointer_check &&
        !enable_pointer_primitive_check &&
        instruction.assign_lhs().id() == ID_symbol &&
        to_symbol_expr(instruction.assign_lhs()).get_identifier() ==
          CPROVER_PREFIX "dead_object")
      {
        instruction.turn_into_skip();
        added_skip = true;
        continue;
      }
      else
#endif
      if(!instruction.is_assert())
        continue;

      const irep_idt &property_class =
        instruction.source_location().get_property_class();
      auto entry_it = should_skip.find(property_class);
      bool skip = entry_it != should_skip.end() && entry_it->second;

      if(!skip && property_class == "error label")
      {
        const std::string comment =
          id2string(instruction.source_location().get_comment());
        skip = true;
        for(const auto &l : error_labels)
        {
          if(comment == std::string("error label " + l))
          {
            skip = false;
            break;
          }
        }
      }
      else if(!skip && property_class == "overflow")
      {
        const std::string comment =
          id2string(instruction.source_location().get_comment());
        if(has_prefix(comment, "result of signed mod is not representable"))
          skip = !enable_signed_overflow_check;
        else if(has_prefix(comment, "arithmetic overflow on "))
        {
          const std::string op = comment.substr(23);
          if(has_prefix(op, "floating-point "))
            skip = !enable_float_overflow_check;
          else if(
            has_prefix(op, "signed type ") || has_prefix(op, "float to ") ||
            has_prefix(op, "signed to ") || has_prefix(op, "unsigned to "))
          {
            skip = !enable_conversion_check;
          }
          else if(has_prefix(op, "signed "))
          {
            // TODO: some of these checks may also have been generated via
            // enable_pointer_overflow_check
            skip = !enable_signed_overflow_check;
          }
          else if(has_prefix(op, "unsigned "))
          {
            // TODO: some of these checks may also have been generated via
            // enable_pointer_overflow_check
            skip = !enable_unsigned_overflow_check;
          }
        }
      }

      if(skip)
      {
        instruction.turn_into_skip();
        added_skip = true;
      }
      else
      {
        if(enable_assert_to_assume)
          instruction.turn_into_assume();

          // TODO: the following would also simplify assertions not generated by
          // goto_check_c
#if 0
        if(enable_simplify)
          simplify(instruction.guard, ns);

        if(!retain_trivial && instruction.guard.is_true())
        {
          instruction.turn_into_skip();
          added_skip = true;
        }
#endif
      }
    }

    if(added_skip)
      remove_skip(entry.second.body);
  }
}
