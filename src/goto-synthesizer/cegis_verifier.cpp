/*******************************************************************\

Module: Verifier for Counterexample-Guided Synthesis

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Verifier for Counterexample-Guided Synthesis

#include "cegis_verifier.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/options.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/prefix.h>

#include <goto-programs/goto_convert_functions.h>
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
#include <goto-instrument/contracts/instrument_spec_assigns.h>
#include <goto-instrument/contracts/utils.h>
#include <goto-instrument/havoc_utils.h>
#include <langapi/language_util.h>
#include <pointer-analysis/add_failed_symbols.h>
#include <solvers/prop/prop.h>

static bool contains_symbol_prefix(const exprt &expr, const std::string &prefix)
{
  for(auto it = expr.depth_begin(), itend = expr.depth_end(); it != itend; ++it)
  {
    if(
      expr.id() == ID_symbol &&
      has_prefix(id2string(to_symbol_expr(expr).get_identifier()), prefix))
    {
      return true;
    }
  }
  return false;
}

static const exprt &
get_checked_pointer_from_null_pointer_check(const exprt &violation)
{
  // A NULL-pointer check is the negation of an equation between the checked
  // pointer and a NULL pointer.
  // ! (POINTER_OBJECT(NULL) == POINTER_OBJECT(ptr))
  const equal_exprt &equal_expr = to_equal_expr(to_not_expr(violation).op());

  const pointer_object_exprt &lhs_pointer_object =
    to_pointer_object_expr(equal_expr.lhs());
  const pointer_object_exprt &rhs_pointer_object =
    to_pointer_object_expr(equal_expr.rhs());

  const exprt &lhs_pointer = lhs_pointer_object.operands()[0];
  const exprt &rhs_pointer = rhs_pointer_object.operands()[0];

  // NULL == ptr
  if(
    can_cast_expr<constant_exprt>(lhs_pointer) &&
    is_null_pointer(*expr_try_dynamic_cast<constant_exprt>(lhs_pointer)))
  {
    return rhs_pointer;
  }

  // Not a equation with NULL on one side.
  UNREACHABLE;
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

  // Generating trace for counterexamples.
  options.set_option("trace", true);

  // Preprocess `goto_model`. Copied from `cbmc_parse_options.cpp`.
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

cext::violation_typet
cegis_verifiert::extract_violation_type(const std::string &description)
{
  // The violation is a pointer OOB check.
  if((description.find(
        "dereference failure: pointer outside object bounds in") !=
      std::string::npos))
  {
    return cext::violation_typet::cex_out_of_boundary;
  }

  // The violation is a null pointer check.
  if(description.find("pointer NULL") != std::string::npos)
  {
    return cext::violation_typet::cex_null_pointer;
  }

  // The violation is a loop-invariant-preservation check.
  if(description.find("preserved") != std::string::npos)
  {
    return cext::violation_typet::cex_not_preserved;
  }

  // The violation is a loop-invariant-preservation check.
  if(description.find("invariant before entry") != std::string::npos)
  {
    return cext::violation_typet::cex_not_hold_upon_entry;
  }

  // The violation is an assignable check.
  if(description.find("assignable") != std::string::npos)
  {
    return cext::violation_typet::cex_assignable;
  }

  return cext::violation_typet::cex_other;
}

std::list<loop_idt>
cegis_verifiert::get_cause_loop_id_for_assigns(const goto_tracet &goto_trace)
{
  std::list<loop_idt> result;

  // We say a loop is the cause loop of an assignable-violation if the inclusion
  // check is in the loop.

  // So we check what loops the last step of the trace is in.
  // Transformed loop head:
  // ASSIGN entered_loop = false
  // Transformed loop end:
  // ASSIGN entered_loop = true
  for(const auto &step : goto_trace.steps)
  {
    // We are entering a loop.
    if(is_transformed_loop_head(step.pc))
    {
      result.push_front(
        loop_idt(step.function_id, original_loop_number_map[step.pc]));
    }
    // We are leaving a loop.
    else if(is_transformed_loop_end(step.pc))
    {
      const loop_idt loop_id(
        step.function_id, original_loop_number_map[step.pc]);
      INVARIANT(
        result.front() == loop_id, "Leaving a loop we haven't entered.");
      result.pop_front();
    }
  }

  INVARIANT(!result.empty(), "The assignable violation is not in a loop.");
  return result;
}

std::list<loop_idt> cegis_verifiert::get_cause_loop_id(
  const goto_tracet &goto_trace,
  const goto_programt::const_targett violation)
{
  std::list<loop_idt> result;

  // build the dependence graph
  const namespacet ns(goto_model.symbol_table);
  dependence_grapht dependence_graph(ns);
  dependence_graph(goto_model);

  // Checking if `to` is dependent on `from`.
  // `from` : loop havocing
  // `to`   : violation

  // Get `to`---the instruction where the violation happens
  irep_idt to_fun_name = goto_trace.get_last_step().function_id;
  const goto_functionst::goto_functiont &to_function =
    goto_model.get_goto_function(to_fun_name);
  goto_programt::const_targett to = to_function.body.instructions.end();
  for(goto_programt::const_targett it = to_function.body.instructions.begin();
      it != to_function.body.instructions.end();
      ++it)
  {
    if(it->location_number == violation->location_number)
    {
      to = it;
    }
  }

  INVARIANT(
    to != to_function.body.instructions.end(),
    "There must be a violation in a trace.");

  // Compute the backward reachable set.
  const auto reachable_vector =
    dependence_graph.get_reachable(dependence_graph[to].get_node_id(), false);
  const std::set<size_t> reachable_set =
    std::set<size_t>(reachable_vector.begin(), reachable_vector.end());

  // A loop is the cause loop if the violation is dependent on the write set of
  // the loop.
  for(const auto &step : goto_trace.steps)
  {
    // Being dependent on a write set is equivalent to being dependent on one
    // of the loop havocing instruction.
    if(loop_havoc_set.count(step.pc))
    {
      // Get `from`---a loop havoc instruction.
      irep_idt from_fun_name = step.function_id;
      const goto_functionst::goto_functiont &from_function =
        goto_model.get_goto_function(from_fun_name);
      goto_programt::const_targett from = from_function.body.instructions.end();
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

      INVARIANT(
        from != from_function.body.instructions.end(),
        "Failed to find the location number of the loop havoc.");

      // The violation is caused by the loop havoc
      // if it is dependent on the loop havoc.
      if(reachable_set.count(dependence_graph[from].get_node_id()))
      {
        result.push_back(
          loop_idt(step.function_id, original_loop_number_map[step.pc]));
        return result;
      }
    }
  }
  return result;
}

cext::violation_locationt cegis_verifiert::get_violation_location(
  const loop_idt &loop_id,
  const goto_functiont &function,
  unsigned location_number_of_target)
{
  if(is_instruction_in_transformed_loop_condition(
       loop_id, function, location_number_of_target))
  {
    return cext::violation_locationt::in_condition;
  }

  if(is_instruction_in_transformed_loop(
       loop_id, function, location_number_of_target))
  {
    return cext::violation_locationt::in_loop;
  }

  return cext::violation_locationt::after_loop;
}

bool cegis_verifiert::is_instruction_in_transformed_loop_condition(
  const loop_idt &loop_id,
  const goto_functiont &function,
  unsigned location_number_of_target)
{
  // The transformed loop condition is a set of instructions from
  // loop havocing instructions
  // to
  // if(!guard) GOTO EXIT
  unsigned location_number_of_havocing = 0;
  for(auto it = function.body.instructions.begin();
      it != function.body.instructions.end();
      ++it)
  {
    // Record the location number of the beginning of a transformed loop.
    if(
      loop_havoc_set.count(it) &&
      original_loop_number_map[it] == loop_id.loop_number)
    {
      location_number_of_havocing = it->location_number;
    }

    // Reach the end of the evaluation of the transformed loop condition.
    if(location_number_of_havocing != 0 && it->is_goto())
    {
      if((location_number_of_havocing < location_number_of_target &&
          location_number_of_target < it->location_number))
      {
        return true;
      }
      location_number_of_havocing = 0;
    }
  }
  return false;
}

bool cegis_verifiert::is_instruction_in_transformed_loop(
  const loop_idt &loop_id,
  const goto_functiont &function,
  unsigned location_number_of_target)
{
  // The loop body after transformation are instructions from
  // loop havocing instructions
  // to
  // loop end of transformed code.
  unsigned location_number_of_havocing = 0;

  for(goto_programt::const_targett it = function.body.instructions.begin();
      it != function.body.instructions.end();
      ++it)
  {
    // Record the location number of the begin of a transformed loop.
    if(
      loop_havoc_set.count(it) &&
      original_loop_number_map[it] == loop_id.loop_number)
    {
      location_number_of_havocing = it->location_number;
    }

    // Reach the end of a transformed loop.
    if(
      is_transformed_loop_end(it) &&
      original_loop_number_map[it] == loop_id.loop_number)
    {
      INVARIANT(
        location_number_of_havocing != 0,
        "We must have entered the transformed loop before reaching the end");

      // Check if `location_number_of_target` is between the begin and the end
      // of the transformed loop.
      if((location_number_of_havocing < location_number_of_target &&
          location_number_of_target < it->location_number))
      {
        return true;
      }
    }
  }

  return false;
}

cext cegis_verifiert::build_cex(
  const goto_tracet &goto_trace,
  const source_locationt &loop_entry_loc)
{
  const namespacet ns(goto_model.symbol_table);

  // Valuations of havoced variables right after havoc instructions.
  std::unordered_map<exprt, mp_integer, irep_hash> object_sizes;
  std::unordered_map<exprt, mp_integer, irep_hash> havoced_values;
  std::unordered_map<exprt, mp_integer, irep_hash> havoced_pointer_offsets;

  // Loop-entry valuations of havoced variables.
  std::unordered_map<exprt, mp_integer, irep_hash> loop_entry_values;
  std::unordered_map<exprt, mp_integer, irep_hash> loop_entry_offsets;

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
           step.full_lhs.type().id() == ID_signedbv ||
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
        if(
          step.full_lhs.type().id() == ID_unsignedbv ||
          step.full_lhs.type().id() == ID_signedbv)
        {
          bool is_signed = step.full_lhs.type().id() == ID_signedbv;
          const auto &bv_type =
            type_try_dynamic_cast<bitvector_typet>(step.full_lhs.type());
          const auto width = bv_type->get_width();
          // Store the value into the map for loop_entry value if we haven't
          // entered the loop.
          if(!entered_loop)
          {
            loop_entry_values[step.full_lhs] = bvrep2integer(
              step.full_lhs_value.get_string(ID_value), width, is_signed);
          }

          // Store the value into the the map for havoced value if this step
          // is a loop havocing instruction.
          if(loop_havoc_set.count(step.pc))
          {
            havoced_values[step.full_lhs] = bvrep2integer(
              step.full_lhs_value.get_string(ID_value), width, is_signed);
          }
        }

        // Record object_size, pointer_offset, and loop_entry(pointer_offset).
        if(
          can_cast_expr<annotated_pointer_constant_exprt>(
            step.full_lhs_value) &&
          contains_symbol_prefix(
            step.full_lhs_value, SYMEX_DYNAMIC_PREFIX "::dynamic_object"))
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
          mp_integer object_size =
            pointer_offset_size(to_array_type(underlying_array.type()), ns)
              .value();
          object_sizes[step.full_lhs] = object_size;

          // Extract offsets.
          mp_integer offset = 0;
          if(pointer_arithmetic.offset.is_not_nil())
          {
            constant_exprt offset_expr =
              expr_dynamic_cast<constant_exprt>(pointer_arithmetic.offset);
            offset = bvrep2integer(
              offset_expr.get_value(), size_type().get_width(), false);
          }

          // Store the offset into the map for loop_entry if we haven't
          // entered the loop.
          if(!entered_loop)
          {
            loop_entry_offsets[step.full_lhs] = offset;
          }

          // Store the offset into the the map for havoced offset if this step
          // is a loop havocing instruction.
          if(loop_havoc_set.count(step.pc))
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

optionalt<cext> cegis_verifiert::verify()
{
  // This method does the following three things to verify the `goto_model` and
  // return a formatted counterexample if there is any violated property.
  //
  // 1. annotate and apply the loop contracts stored in `invariant_candidates`.
  //
  // 2. run the CBMC API to verify the instrumented goto model. As the API is
  //    not merged yet, we preprocess the goto model and run the symex checker
  //    on it to simulate CBMC API.
  // TODO: ^^^ replace the symex checker once the real API is merged.
  //
  // 3. construct the formatted counterexample from the violated property and
  //    its trace.

  // Store the original functions. We will restore them after the verification.
  for(const auto &fun_entry : goto_model.goto_functions.function_map)
  {
    original_functions[fun_entry.first].copy_from(fun_entry.second.body);
  }

  // Annotate the candidates to the goto_model for checking.
  annotate_invariants(invariant_candidates, goto_model);

  // Annotate assigns
  annotate_assigns(assigns_map, goto_model);

  // Control verbosity. We allow non-error output message only when verbosity
  // is set to larger than messaget::M_DEBUG.
  const unsigned original_verbosity = log.get_message_handler().get_verbosity();
  if(original_verbosity < messaget::M_DEBUG)
    log.get_message_handler().set_verbosity(messaget::M_ERROR);

  // Apply loop contracts we annotated.
  code_contractst cont(goto_model, log);
  cont.apply_loop_contracts();
  original_loop_number_map = cont.get_original_loop_number_map();
  loop_havoc_set = cont.get_loop_havoc_set();

  // Get the checker same as CBMC api without any flag.
  // TODO: replace the checker with CBMC api once it is implemented.
  ui_message_handlert ui_message_handler(log.get_message_handler());
  const auto options = get_options();
  std::unique_ptr<
    all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>>
    checker = util_make_unique<
      all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>>(
      options, ui_message_handler, goto_model);

  goto_convert(
    goto_model.symbol_table,
    goto_model.goto_functions,
    log.get_message_handler());

  // Run the checker to get the result.
  const resultt result = (*checker)();

  if(original_verbosity >= messaget::M_DEBUG)
    checker->report();

  // Restore the verbosity.
  log.get_message_handler().set_verbosity(original_verbosity);

  //
  // Start to construct the counterexample.
  //

  if(result == resultt::PASS)
  {
    restore_functions();
    return optionalt<cext>();
  }

  if(result == resultt::ERROR || result == resultt::UNKNOWN)
  {
    INVARIANT(false, "Verification failed during loop contract synthesis.");
  }

  properties = checker->get_properties();
  bool target_violation_found = false;
  auto target_violation_info = properties.begin()->second;

  // Find target violation---the violation we want to fix next.
  // A target violation is an assignable violation or the first violation that
  // is not assignable violation.
  for(const auto &property : properties)
  {
    if(property.second.status != property_statust::FAIL)
      continue;

    // assignable violation found
    if(property.second.description.find("assignable") != std::string::npos)
    {
      target_violation = property.first;
      target_violation_info = property.second;
      break;
    }

    // Store the violation that we want to fix with synthesized
    // assigns/invariant.
    if(!target_violation_found)
    {
      target_violation = property.first;
      target_violation_info = property.second;
      target_violation_found = true;
    }
  }

  // Decide the violation type from the description of violation
  cext::violation_typet violation_type =
    extract_violation_type(target_violation_info.description);

  // Compute the cause loop---the loop for which we synthesize loop contracts,
  // and the counterexample.

  // If the violation is an assignable check, we synthesize assigns targets.
  // In the case, cause loops are all loops the violation is in. We keep
  // adding the new assigns target to the most-inner loop that does not
  // contain the new target until the assignable violation is resolved.

  // For other cases, we synthesize loop invariant clauses. We synthesize
  // invariants for one loop at a time. So we return only the first cause loop
  // although there can be multiple ones.

  log.debug() << "Start to compute cause loop ids." << messaget::eom;
  log.debug() << "Violation description: " << target_violation_info.description
              << messaget::eom;

  const auto &trace = checker->get_traces()[target_violation];
  // Doing assigns-synthesis or invariant-synthesis
  if(violation_type == cext::violation_typet::cex_assignable)
  {
    cext result(violation_type);
    result.cause_loop_ids = get_cause_loop_id_for_assigns(trace);
    result.checked_pointer = static_cast<const exprt &>(
      target_violation_info.pc->condition().find(ID_checked_assigns));
    restore_functions();
    return result;
  }

  // We construct the full counterexample only for violations other than
  // assignable checks.

  // Although there can be multiple cause loop ids. We only synthesize
  // loop invariants for the first cause loop.
  const std::list<loop_idt> cause_loop_ids =
    get_cause_loop_id(trace, target_violation_info.pc);

  if(cause_loop_ids.empty())
  {
    log.debug() << "No cause loop found!" << messaget::eom;
    restore_functions();

    return cext(violation_type);
  }

  log.debug() << "Found cause loop with function id: "
              << cause_loop_ids.front().function_id
              << ", and loop number: " << cause_loop_ids.front().loop_number
              << messaget::eom;

  auto violation_location = cext::violation_locationt::in_loop;
  // We always strengthen in_clause if the violation is
  // invariant-not-preserved.
  if(violation_type != cext::violation_typet::cex_not_preserved)
  {
    // Get the location of the violation
    violation_location = get_violation_location(
      cause_loop_ids.front(),
      goto_model.get_goto_function(cause_loop_ids.front().function_id),
      target_violation_info.pc->location_number);
  }

  restore_functions();

  auto return_cex = build_cex(
    trace,
    get_loop_head(
      cause_loop_ids.front().loop_number,
      goto_model.goto_functions
        .function_map[cause_loop_ids.front().function_id])
      ->source_location());
  return_cex.violated_predicate = target_violation_info.pc->condition();
  return_cex.cause_loop_ids = cause_loop_ids;
  return_cex.violation_location = violation_location;
  return_cex.violation_type = violation_type;

  // The pointer checked in the null-pointer-check violation.
  if(violation_type == cext::violation_typet::cex_null_pointer)
  {
    return_cex.checked_pointer = get_checked_pointer_from_null_pointer_check(
      target_violation_info.pc->condition());
  }

  return return_cex;
}
