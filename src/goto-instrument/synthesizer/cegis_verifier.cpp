/*******************************************************************\

Module: Verifier for Counterexample-Guided Synthesis

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Verifier for Counterexample-Guided Synthesis

#include "cegis_verifier.h"

#include <util/arith_tools.h>
#include <util/options.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/prefix.h>

#include <goto-programs/link_to_library.h>
#include <goto-programs/pointer_arithmetic.h>
#include <goto-programs/process_goto_program.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/set_properties.h>

#include <analyses/dependence_graph.h>
#include <ansi-c/cprover_library.h>
#include <assembler/remove_asm.h>
#include <cpp/cprover_library.h>
#include <goto-checker/all_properties_verifier_with_trace_storage.h>
#include <goto-checker/multi_path_symex_checker.h>
#include <goto-instrument/contracts/contracts.h>
#include <goto-instrument/contracts/utils.h>
#include <goto-instrument/havoc_utils.h>
#include <langapi/language_util.h>
#include <pointer-analysis/add_failed_symbols.h>
#include <solvers/prop/prop.h>

static bool contains_symbol_prefix(const exprt &expr, const std::string &prefix)
{
  if(
    expr.id() == ID_symbol &&
    has_prefix(id2string(to_symbol_expr(expr).get_identifier()), prefix))
  {
    return true;
  }

  forall_operands(it, expr)
  {
    if(contains_symbol_prefix(*it, prefix))
      return true;
  }
  return false;
}

optionst cegis_verifiert::get_options()
{
  optionst options;

  // Default options
  // These options are the same as we run CBMC without any set flag.
  options.set_option("built-in-assertions", true);
  options.set_option("propagation", true);
  options.set_option("simple-slice", true);
  options.set_option("simplify", true);
  options.set_option("show-goto-symex-steps", false);
  options.set_option("show-points-to-sets", false);
  options.set_option("show-array-constraints", false);
  options.set_option("built-in-assertions", true);
  options.set_option("assertions", true);
  options.set_option("assumptions", true);
  options.set_option("arrays-uf", "auto");
  options.set_option("depth", UINT32_MAX);
  options.set_option("exploration-strategy", "lifo");
  options.set_option("symex-cache-dereferences", false);
  options.set_option("rewrite-union", true);
  options.set_option("self-loops-to-assumptions", true);
  options.set_option("trace", true);

  // Preporcess `goto_model`. Copied from `cbmc_parse_options.cpp`.
  remove_asm(goto_model);
  link_to_library(
    goto_model, log.get_message_handler(), cprover_cpp_library_factory);
  link_to_library(
    goto_model, log.get_message_handler(), cprover_c_library_factory);
  process_goto_program(goto_model, options, log);

  add_failed_symbols(goto_model.symbol_table);

  remove_skip(goto_model);
  label_properties(goto_model);
  return options;
}

loop_idt cegis_verifiert::get_cause_loop_id(
  const goto_tracet &goto_trace,
  const goto_programt::const_targett violation)
{
  loop_idt result;

  // build the dependence graph
  const namespacet ns(goto_model.symbol_table);
  dependence_grapht dependence_graph(ns);
  dependence_graph(goto_model);

  // A loop is the cause loop if the violation is dependent on the write set of
  // the loop.
  for(const auto &step : goto_trace.steps)
  {
    // Being dependent on a write set is equivalent to being dependent on one
    // of the loop havocing instruction.
    if(is_loop_havoc(*step.pc))
    {
      // Checking if `to` is dependent on `from`.
      // `from` : loop havocing
      // `to`   : violation
      goto_programt::const_targett from;
      goto_programt::const_targett to;

      // Get `from`---a loop havoc instruction.
      irep_idt from_fun_name = step.function_id;
      const goto_functionst::goto_functiont &from_function =
        goto_model.get_goto_function(from_fun_name);
      for(goto_programt::const_targett it =
            from_function.body.instructions.begin();
          it != from_function.body.instructions.end();
          ++it)
      {
        if(it->location_number == step.pc->location_number)
        {
          from = it;
        }
      }

      // Get `to`---the instruction where the violation happens
      irep_idt to_fun_name = goto_trace.get_last_step().function_id;
      const goto_functionst::goto_functiont &to_function =
        goto_model.get_goto_function(to_fun_name);
      for(goto_programt::const_targett it =
            to_function.body.instructions.begin();
          it != to_function.body.instructions.end();
          ++it)
      {
        if(it->location_number == violation->location_number)
        {
          to = it;
        }
      }

      // The violation is caused by the loop havoc
      // if it is dependent on the loop havoc.
      if(dependence_graph.is_flow_dependent(from, to))
      {
        // TODO: not safe for inlined static functions.
        result.function_id = step.pc->source_location().get_function();
        result.loop_number = step.pc->loop_number;
      }
    }
  }
  return result;
}

cext cegis_verifiert::build_cex(
  const goto_tracet &goto_trace,
  const source_locationt &loop_entry_loc)
{
  const namespacet ns(goto_model.symbol_table);

  // Valuations of havoced variables right after havoc instructions.
  std::map<exprt, std::size_t> object_sizes;
  std::map<exprt, std::size_t> havoced_values;
  std::map<exprt, std::size_t> havoced_pointer_offsets;

  // Loop-entry valuations of havoced variables.
  std::map<exprt, std::size_t> loop_entry_values;
  std::map<exprt, std::size_t> loop_entry_offsets;

  // Live variables upon the loop head.
  std::set<exprt> live_variables;

  bool entered_loop = false;

  // Scan the trace step by step to store needed valuations.
  for(const auto &step : goto_trace.steps)
  {
    switch(step.type)
    {
    case goto_trace_stept::typet::DECL:
    case goto_trace_stept::typet::ASSIGNMENT:
    {
      if(!step.full_lhs_value.is_nil())
      {
        // Entered loop?
        if(is_assignment_to_instrumented_variable(step.pc, ENTERED_LOOP))
          entered_loop = step.full_lhs_value == true_exprt();

        // skip hidden steps
        if(step.hidden)
          break;

        // Live variables
        // 1. must be in the same function as the target loop;
        // 2. alive before entering the target loop;
        // 3. a pointer or a primitive-typed variable;
        // TODO: add support for union pointer
        if(
          step.pc->source_location().get_function() ==
            loop_entry_loc.get_function() &&
          !entered_loop &&
          (step.full_lhs.type().id() == ID_unsignedbv ||
           step.full_lhs.type().id() == ID_pointer) &&
          step.full_lhs.id() == ID_symbol)
        {
          const auto &symbol =
            expr_try_dynamic_cast<symbol_exprt>(step.full_lhs);

          // malloc_size is not-hidden tmp variable.
          if(id2string(symbol->get_identifier()) != "malloc::malloc_size")
          {
            live_variables.emplace(step.full_lhs);
          }
        }

        // Record valuation of primitive-typed variable.
        if(step.full_lhs.type().id() == ID_unsignedbv)
        {
          // Store the value into the map for loop_entry value if we haven't
          // entered the loop.
          if(!entered_loop)
          {
            loop_entry_values[step.full_lhs] =
              hex_to_size_t(step.full_lhs_value.get_string(ID_value));
          }

          // Store the value into the the map for havoced value if this step
          // is a loop havocing instruction.
          if(is_loop_havoc(*step.pc))
          {
            havoced_values[step.full_lhs] =
              hex_to_size_t(step.full_lhs_value.get_string(ID_value));
          }
        }

        // Record object_size, pointer_offset, and loop_entry(pointer_offset).
        if(
          can_cast_expr<annotated_pointer_constant_exprt>(
            step.full_lhs_value) &&
          contains_symbol_prefix(
            step.full_lhs_value, SYMEX_DYNAMIC_PREFIX "dynamic_object"))
        {
          const auto &pointer_constant_expr =
            expr_try_dynamic_cast<annotated_pointer_constant_exprt>(
              step.full_lhs_value);

          pointer_arithmetict pointer_arithmetic(
            pointer_constant_expr->symbolic_pointer());
          if(pointer_constant_expr->symbolic_pointer().id() == ID_typecast)
          {
            pointer_arithmetic = pointer_arithmetict(
              pointer_constant_expr->symbolic_pointer().operands()[0]);
          }

          // Extract object size.
          exprt &underlying_array = pointer_arithmetic.pointer;
          // Object sizes are stored in the type of underlying arrays.
          while(!can_cast_type<array_typet>(underlying_array.type()))
          {
            if(
              underlying_array.id() == ID_address_of ||
              underlying_array.id() == ID_index)
            {
              underlying_array = underlying_array.operands()[0];
              continue;
            }
            UNREACHABLE;
          }
          std::size_t object_size =
            pointer_offset_size(to_array_type(underlying_array.type()), ns)
              .value()
              .to_ulong();
          object_sizes[step.full_lhs] = object_size;

          // Extract offsets.
          std::size_t offset = 0;
          if(pointer_arithmetic.offset.is_not_nil())
          {
            constant_exprt offset_expr =
              expr_dynamic_cast<constant_exprt>(pointer_arithmetic.offset);
            offset = hex_to_size_t(id2string(offset_expr.get_value()));
          }

          // Store the offset into the map for loop_entry if we haven't
          // entered the loop.
          if(!entered_loop)
          {
            loop_entry_offsets[step.full_lhs] = offset;
          }

          // Store the offset into the the map for havoced offset if this step
          // is a loop havocing instruction.
          if(is_loop_havoc(*step.pc))
          {
            havoced_pointer_offsets[step.full_lhs] = offset;
          }
        }
      }
    }

    case goto_trace_stept::typet::ASSERT:
    case goto_trace_stept::typet::FUNCTION_CALL:
    case goto_trace_stept::typet::FUNCTION_RETURN:
    case goto_trace_stept::typet::ASSUME:
    case goto_trace_stept::typet::LOCATION:
    case goto_trace_stept::typet::GOTO:
    case goto_trace_stept::typet::OUTPUT:
    case goto_trace_stept::typet::INPUT:
    case goto_trace_stept::typet::SPAWN:
    case goto_trace_stept::typet::MEMORY_BARRIER:
    case goto_trace_stept::typet::ATOMIC_BEGIN:
    case goto_trace_stept::typet::ATOMIC_END:
    case goto_trace_stept::typet::DEAD:
    case goto_trace_stept::typet::CONSTRAINT:
    case goto_trace_stept::typet::SHARED_READ:
    case goto_trace_stept::typet::SHARED_WRITE:
      break;

    case goto_trace_stept::typet::NONE:
      UNREACHABLE;
    }
  }

  return cext(
    object_sizes,
    havoced_values,
    havoced_pointer_offsets,
    loop_entry_values,
    loop_entry_offsets,
    live_variables);
}

void cegis_verifiert::restore_functions()
{
  for(const auto &fun_entry : goto_model.goto_functions.function_map)
  {
    irep_idt fun_name = fun_entry.first;
    goto_model.goto_functions.function_map[fun_name].body.swap(
      original_functions[fun_name]);
  }
}

bool cegis_verifiert::verify()
{
  // This method does the following three things to verify the `goto_model` and
  // return a formatted counterexample if there is any violated property.
  //
  // 1. annotate and apply the loop contracts stored in `invariant_candidates`.
  //
  // 2. run the CBMC API to verify the intrumented goto model. As the API is not
  //    merged yet, we preprocess the goto model and run the symex checker on it
  //    to simulate CBMC API.
  //    FIXEME: ^^^ replace the symex checker once the real API is merged.
  //
  // 3. construct the formatted counterexample from the violated property and
  //    its trace.

  // Store the original functions. We will restore them after the verification.
  for(const auto &fun_entry : goto_model.goto_functions.function_map)
  {
    original_functions[fun_entry.first].copy_from(fun_entry.second.body);
  }

  // Annotate the candidates tot the goto_model for checking.
  annotate_invariants(invariant_candidates, goto_model);

  // Control verbosity.
  // We allow non-error output message only when verbosity is set to at least 9.
  const unsigned original_verbosity = log.get_message_handler().get_verbosity();
  if(original_verbosity < 9)
    log.get_message_handler().set_verbosity(1);

  // Apply loop contracts we annotated.
  code_contractst cont(goto_model, log);
  cont.apply_loop_contracts();

  // Get the checker same as CBMC api without any flag.
  // TODO: replace the checker with CBMC api once it is implemented.
  ui_message_handlert ui_message_handler(log.get_message_handler());
  const auto options = get_options();
  std::unique_ptr<
    all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>>
    checker = util_make_unique<
      all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>>(
      options, ui_message_handler, goto_model);

  // Run the checker to get the result.
  const resultt result = (*checker)();

  if(original_verbosity >= 9)
    checker->report();

  // Restore the verbosity.
  log.get_message_handler().set_verbosity(original_verbosity);

  //
  // Strat to counstruct the counterexample.
  //

  if(result == resultt::PASS)
  {
    restore_functions();
    return true;
  }

  if(result == resultt::ERROR || result == resultt::UNKNOWN)
  {
    INVARIANT(false, "Verification failed during loop contract synthesis.");
  }

  properties = checker->get_properties();
  // Find the violation and construct conterexample from its trace.
  for(const auto &property_it : properties)
  {
    if(property_it.second.status != property_statust::FAIL)
      continue;

    first_violation = property_it.first;
    exprt violated_predicate = property_it.second.pc->condition();

    // The pointer checked in the null-pointer-check violation.
    exprt checked_pointer = true_exprt();

    // Type of the violation
    cext::violation_typet violation_type = cext::violation_typet::cex_other;

    // The violation is a pointer OOB check.
    if((property_it.second.description.find(
          "dereference failure: pointer outside object bounds in") !=
        std::string::npos))
    {
      violation_type = cext::violation_typet::cex_out_of_boundary;
    }

    // The violation is a null pointer check.
    if(property_it.second.description.find("pointer NULL") != std::string::npos)
    {
      violation_type = cext::violation_typet::cex_null_pointer;
      checked_pointer = property_it.second.pc->condition()
                          .operands()[0]
                          .operands()[1]
                          .operands()[0];
      INVARIANT(checked_pointer.id() == ID_symbol, "Checking pointer symbol");
    }

    // The violation is a loop-invariant-preservation check.
    if(property_it.second.description.find("preserved") != std::string::npos)
    {
      violation_type = cext::violation_typet::cex_not_preserved;
    }

    // The violation is a loop-invariant-preservation check.
    if(
      property_it.second.description.find("invariant before entry") !=
      std::string::npos)
    {
      violation_type = cext::violation_typet::cex_not_hold_upon_entry;
    }

    // The loop which could be the cause of the violation.
    // We say a loop is the cause loop if the violated predicate is dependent
    // upon the write set of the loop.
    loop_idt cause_loop_id = get_cause_loop_id(
      checker->get_traces()[property_it.first], property_it.second.pc);

    if(!cause_loop_id.loop_number.has_value())
    {
      log.debug() << "No cause loop found!\n";
      restore_functions();

      return_cex.cause_loop_id = cause_loop_id;
      return_cex.cex_type = violation_type;
      return false;
    }

    log.debug() << "Found cause loop with function id: "
                << cause_loop_id.function_id
                << ", and loop number: " << cause_loop_id.loop_number.value()
                << "\n";

    // Decide whether the violation is in the cause loop.
    bool violation_in_loop = is_instruction_in_transfomed_loop(
      cause_loop_id,
      goto_model.get_goto_function(cause_loop_id.function_id),
      property_it.second.pc->location_number);

    // We always strengthen in_clause if the violation is
    // invariant-not-preserved.
    if(violation_type == cext::violation_typet::cex_not_preserved)
      violation_in_loop = true;

    restore_functions();

    return_cex = build_cex(
      checker->get_traces()[property_it.first],
      get_loop_head(
        cause_loop_id.loop_number.value(),
        goto_model.goto_functions.function_map[cause_loop_id.function_id])
        ->source_location());
    return_cex.violated_predicate = violated_predicate;
    return_cex.cause_loop_id = cause_loop_id;
    return_cex.checked_pointer = checked_pointer;
    return_cex.is_violation_in_loop = violation_in_loop;
    return_cex.cex_type = violation_type;

    return false;
  }

  UNREACHABLE;
}
