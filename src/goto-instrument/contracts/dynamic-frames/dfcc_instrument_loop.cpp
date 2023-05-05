/*******************************************************************\

Module: Dynamic frame condition checking for loop contracts

Author: Qinheping Hu, qinhh@amazon.com

Author: Remi Delmas, delmasrd@amazon.com

Date: April 2023

\*******************************************************************/

#include "dfcc_instrument_loop.h"
#include <goto-programs/goto_convert_class.h>

#include <util/format_expr.h>
#include <util/fresh_symbol.h>

#include <goto-instrument/contracts/utils.h>

#include "dfcc_cfg_info.h"
#include "dfcc_contract_clauses_codegen.h"
#include "dfcc_instrument.h"
#include "dfcc_loop_tags.h"
#include "dfcc_spec_functions.h"

dfcc_instrument_loopt::dfcc_instrument_loopt(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  dfcc_spec_functionst &spec_functions,
  dfcc_contract_clauses_codegent &contract_clauses_codegen)
  : goto_model(goto_model),
    log(message_handler),
    utils(utils),
    library(library),
    spec_functions(spec_functions),
    contract_clauses_codegen(contract_clauses_codegen),
    ns(goto_model.symbol_table)
{
}

void dfcc_instrument_loopt::operator()(
  const std::size_t loop_id,
  const irep_idt &function_id,
  goto_functiont &goto_function,
  dfcc_cfg_infot &cfg_info,
  const std::set<symbol_exprt> &local_statics,
  std::set<irep_idt> &function_pointer_contracts)
{
  const dfcc_loop_infot &loop = cfg_info.get_loop_info(loop_id);
  const std::size_t cbmc_loop_id = loop.cbmc_loop_id;
  const exprt &outer_write_set = cfg_info.get_outer_write_set(loop_id);
  const irep_idt language_mode = utils.get_function_symbol(function_id).mode;
  goto_programt::targett head = loop.find_head(goto_function.body).value();
  auto head_location(head->source_location());

  auto &symbol_table = goto_model.symbol_table;

  // Temporary variables:
  // Create a temporary to track if we entered the loop,
  // i.e., the loop guard was satisfied.
  const auto entered_loop =
    get_fresh_aux_symbol(
      bool_typet(),
      id2string(function_id),
      std::string(ENTERED_LOOP) + "__" + std::to_string(cbmc_loop_id),
      head_location,
      language_mode,
      symbol_table)
      .symbol_expr();

  // Create a snapshot of the invariant so that we can check the base case,
  // if the loop is not vacuous and must be abstracted with contracts.
  const auto initial_invariant = get_fresh_aux_symbol(
                                   bool_typet(),
                                   id2string(function_id),
                                   INIT_INVARIANT,
                                   head_location,
                                   language_mode,
                                   symbol_table)
                                   .symbol_expr();

  // Create a temporary variable to track base case vs inductive case
  // instrumentation of the loop.
  const auto in_base_case = get_fresh_aux_symbol(
                              bool_typet(),
                              id2string(function_id),
                              IN_BASE_CASE,
                              head_location,
                              language_mode,
                              symbol_table)
                              .symbol_expr();

  // Temporary variables for storing the multidimensional decreases clause
  // at the start of and end of a loop body.
  exprt::operandst decreases_clauses = loop.decreases;
  std::vector<symbol_exprt> old_decreases_vars, new_decreases_vars;
  for(const auto &clause : decreases_clauses)
  {
    // old
    const auto old_decreases_var = get_fresh_aux_symbol(
                                     clause.type(),
                                     id2string(function_id),
                                     "tmp_cc",
                                     head_location,
                                     language_mode,
                                     symbol_table)
                                     .symbol_expr();
    old_decreases_vars.push_back(old_decreases_var);
    // new
    const auto new_decreases_var = get_fresh_aux_symbol(
                                     clause.type(),
                                     id2string(function_id),
                                     "tmp_cc",
                                     head_location,
                                     language_mode,
                                     symbol_table)
                                     .symbol_expr();
    new_decreases_vars.push_back(new_decreases_var);
  }

  // Convert the assigns clause to the required type.
  exprt::operandst assigns(loop.assigns.begin(), loop.assigns.end());

  // Add local statics to the assigns clause.
  for(auto &local_static : local_statics)
  {
    assigns.push_back(local_static);
  }

  auto nof_targets = assigns.size();
  max_assigns_clause_size = std::max(nof_targets, max_assigns_clause_size);

  //   populate(w_loop, <loop_assigns>);
  // Construct the write set from loop assigns target. That is, contract_assigns
  // in the result __CPROVER_contracts_write_set_t should be the set of CAR
  // of the loop assign targets.
  goto_programt assigns_instrs;
  goto_programt write_set_populate_instrs;

  //   havoc(w_loop);
  // The generated GOTO instructions havoc the write set of the loop.
  goto_programt havoc_instrs;
  contract_clauses_codegen.gen_spec_assigns_instructions(
    language_mode, assigns, assigns_instrs);

  spec_functions.generate_havoc_instructions(
    function_id,
    language_mode,
    symbol_table.get_writeable_ref(function_id).module,
    assigns_instrs,
    loop.addr_of_write_set_var,
    havoc_instrs,
    nof_targets);
  spec_functions.to_spec_assigns_instructions(
    loop.addr_of_write_set_var, language_mode, assigns_instrs, nof_targets);
  write_set_populate_instrs.copy_from(assigns_instrs);

  // Replace bound variables by fresh instances in quantified formulas.
  exprt invariant = loop.invariant;
  if(has_subexpr(invariant, ID_exists) || has_subexpr(invariant, ID_forall))
    add_quantified_variable(symbol_table, invariant, language_mode);

  // ---------- Add instrumented instructions ----------
  goto_programt::targett loop_latch =
    loop.find_latch(goto_function.body).value();

  const auto &history_var_map = add_prehead_instructions(
    loop_id,
    goto_function,
    symbol_table,
    head,
    loop_latch,
    write_set_populate_instrs,
    invariant,
    assigns,
    loop.write_set_var,
    loop.addr_of_write_set_var,
    entered_loop,
    initial_invariant,
    in_base_case,
    language_mode);

  const auto step_target = add_step_instructions(
    loop_id,
    cbmc_loop_id,
    function_id,
    goto_function,
    symbol_table,
    head,
    loop_latch,
    havoc_instrs,
    invariant,
    decreases_clauses,
    loop.addr_of_write_set_var,
    outer_write_set,
    initial_invariant,
    in_base_case,
    old_decreases_vars,
    language_mode);

  add_body_instructions(
    loop_id,
    cbmc_loop_id,
    goto_function,
    symbol_table,
    head,
    loop_latch,
    invariant,
    decreases_clauses,
    entered_loop,
    in_base_case,
    old_decreases_vars,
    new_decreases_vars,
    step_target,
    language_mode);

  add_exit_instructions(
    loop_id,
    cbmc_loop_id,
    goto_function,
    head,
    loop.write_set_var,
    loop.addr_of_write_set_var,
    history_var_map,
    entered_loop,
    initial_invariant,
    in_base_case,
    old_decreases_vars,
    new_decreases_vars);

  goto_function.body.update();
}

std::map<exprt, exprt> dfcc_instrument_loopt::add_prehead_instructions(
  const std::size_t loop_id,
  goto_functionst::goto_functiont &goto_function,
  symbol_tablet &symbol_table,
  goto_programt::targett loop_head,
  goto_programt::targett loop_latch,
  goto_programt &assigns_instrs,
  exprt &invariant,
  const exprt::operandst &assigns,
  const symbol_exprt &loop_write_set,
  const symbol_exprt &addr_of_loop_write_set,
  const symbol_exprt &entered_loop,
  const symbol_exprt &initial_invariant,
  const symbol_exprt &in_base_case,
  const irep_idt &language_mode)
{
  auto loop_head_location(loop_head->source_location());
  dfcc_remove_loop_tags(loop_head_location);

  // ```
  //   ... preamble ...
  //
  //   // Prehead block: Declare & initialize instrumentation variables
  //   snapshot loop_entry history vars;
  //   entered_loop = false
  //   initial_invariant = loop_invariant;
  //   in_base_case = true;
  //   __ws_loop;
  //   ws_loop := address_of(__ws_loop);
  //   __write_set_create(ws_loop);
  //   __write_set_add(ws_loop, loop_assigns);
  //   __write_set_add(ws_loop, local_statics);
  //   GOTO HEAD;
  // ```

  goto_programt pre_loop_head_instrs;
  std::map<exprt, exprt> history_var_map;

  // initialize loop_entry history vars;
  {
    // Process "loop_entry" history variables.
    // We find and replace all "__CPROVER_loop_entry" in invariant.
    replace_history_parameter(
      symbol_table,
      invariant,
      history_var_map,
      loop_head_location,
      language_mode,
      pre_loop_head_instrs,
      ID_loop_entry);
  }

  // entered_loop = false
  {
    pre_loop_head_instrs.add(
      goto_programt::make_decl(entered_loop, loop_head_location));
    pre_loop_head_instrs.add(
      goto_programt::make_assignment(entered_loop, false_exprt{}));
  }

  // initial_invariant = <loop_invariant>;
  {
    // Create a snapshot of the invariant so that we can check the base case,
    // if the loop is not vacuous and must be abstracted with contracts.
    pre_loop_head_instrs.add(
      goto_programt::make_decl(initial_invariant, loop_head_location));

    // Although the invariant at this point will not have side effects,
    // it is still a C expression, and needs to be "goto_convert"ed.
    // Note that this conversion may emit many GOTO instructions.
    code_frontend_assignt initial_invariant_assignment{
      initial_invariant, invariant, loop_head_location};
    goto_convertt converter(symbol_table, log.get_message_handler());
    converter.goto_convert(
      initial_invariant_assignment, pre_loop_head_instrs, language_mode);
  }

  {
    // Create a temporary variable to track base case vs inductive case
    // instrumentation of the loop.
    // in_base_case = true;
    pre_loop_head_instrs.add(
      goto_programt::make_decl(in_base_case, loop_head_location));
    pre_loop_head_instrs.add(
      goto_programt::make_assignment(in_base_case, true_exprt{}));
  }

  {
    // Create and populate the write set.
    // DECL loop_write_set
    // DECL addr_of_loop_write_set
    // ASSIGN write_set_ptr := address_of(write_set)
    // CALL __CPROVER_contracts_write_set_create(write_set_ptr,
    //        contracts_assigns_size, contracts_assigns_frees_size,
    //        assume_require_ctx, assert_require_ctx, assume_ensures_ctx,
    //        assert_ensures_ctx, allow_allocate, allow_deallocate);
    pre_loop_head_instrs.add(
      goto_programt::make_decl(loop_write_set, loop_head_location));
    pre_loop_head_instrs.add(
      goto_programt::make_decl(addr_of_loop_write_set, loop_head_location));
    pre_loop_head_instrs.add(goto_programt::make_assignment(
      addr_of_loop_write_set,
      address_of_exprt(loop_write_set),
      loop_head_location));

    code_function_callt call = library.write_set_create_call(
      addr_of_loop_write_set,
      from_integer(assigns.size(), size_type()),
      loop_head_location);
    pre_loop_head_instrs.add(
      goto_programt::make_function_call(call, loop_head_location));

    pre_loop_head_instrs.destructive_append(assigns_instrs);
  }

  // goto HEAD;
  pre_loop_head_instrs.add(
    goto_programt::make_goto(loop_head, true_exprt{}, loop_head_location));

  goto_function.body.destructive_insert(loop_head, pre_loop_head_instrs);
  return history_var_map;
}

goto_programt::instructiont::targett
dfcc_instrument_loopt::add_step_instructions(
  const std::size_t loop_id,
  const std::size_t cbmc_loop_id,
  const irep_idt &function_id,
  goto_functionst::goto_functiont &goto_function,
  symbol_tablet &symbol_table,
  goto_programt::targett loop_head,
  goto_programt::targett loop_latch,
  goto_programt &havoc_instrs,
  const exprt &invariant,
  const exprt::operandst &decreases_clauses,
  const symbol_exprt &addr_of_loop_write_set,
  const exprt &outer_write_set,
  const symbol_exprt &initial_invariant,
  const symbol_exprt &in_base_case,
  const std::vector<symbol_exprt> &old_decreases_vars,
  const irep_idt &language_mode)
{
  auto loop_head_location(loop_head->source_location());
  dfcc_remove_loop_tags(loop_head_location);

  // ```
  // STEP: // Loop step block: havoc the loop state
  //   ASSERT(initial_invariant);
  //   __write_set_check_inclusion(ws_loop, ws_parent);
  //   in_base_case = false;
  //   in_loop_havoc_block = true;
  //   havoc(assigns_clause_targets);
  //   in_loop_havoc_block = false;
  //   ASSUME(loop_invariant);
  //   old_variant = loop_decreases;
  // ```

  goto_programt step_instrs;

  // We skip past it initially, because of the unconditional jump above,
  // but jump back here if we get past the loop guard while in_base_case.
  // `in_base_case = false;`
  goto_programt::instructiont::targett step_case_target =
    step_instrs.add(goto_programt::make_assignment(
      in_base_case, false_exprt{}, loop_head_location));

  {
    // If we jump here, then the loop runs at least once,
    // so add the base case assertion: `assert(initial_invariant)`.
    source_locationt check_location(loop_head_location);
    check_location.set_property_class("loop_invariant_base");
    check_location.set_comment(
      "Check invariant before entry for loop " +
      id2string(check_location.get_function()) + "." +
      std::to_string(cbmc_loop_id));
    step_instrs.add(
      goto_programt::make_assertion(initial_invariant, check_location));
  }

  {
    // Check assigns clause inclusion with parent write set
    // skip the check when if w_parent is NULL.
    auto goto_instruction = step_instrs.add(goto_programt::make_incomplete_goto(
      equal_exprt(
        outer_write_set,
        null_pointer_exprt(to_pointer_type(outer_write_set.type()))),
      loop_head_location));

    auto check_var =
      get_fresh_aux_symbol(
        bool_typet(),
        id2string(function_id),
        "__check_assigns_clause_incl_loop_" + std::to_string(cbmc_loop_id),
        loop_head_location,
        language_mode,
        symbol_table)
        .symbol_expr();

    step_instrs.add(goto_programt::make_decl(check_var, loop_head_location));
    step_instrs.add(goto_programt::make_function_call(
      library.write_set_check_assigns_clause_inclusion_call(
        check_var, outer_write_set, addr_of_loop_write_set, loop_head_location),
      loop_head_location));

    source_locationt check_location(loop_head_location);
    check_location.set_property_class("loop_assigns");
    check_location.set_comment(
      "Check assigns clause inclusion for loop " +
      id2string(check_location.get_function()) + "." +
      std::to_string(cbmc_loop_id));
    step_instrs.add(goto_programt::make_assertion(check_var, check_location));
    step_instrs.add(goto_programt::make_dead(check_var, loop_head_location));

    auto label_instruction =
      step_instrs.add(goto_programt::make_skip(loop_head_location));
    goto_instruction->complete_goto(label_instruction);
  }

  {
    // Generate havocing code for assigns targets.
    const auto in_loop_havoc_block =
      get_fresh_aux_symbol(
        bool_typet(),
        id2string(function_id),
        std::string(IN_LOOP_HAVOC_BLOCK) + +"__" + std::to_string(cbmc_loop_id),
        loop_head_location,
        language_mode,
        symbol_table)
        .symbol_expr();
    step_instrs.add(
      goto_programt::make_decl(in_loop_havoc_block, loop_head_location));
    step_instrs.add(
      goto_programt::make_assignment(in_loop_havoc_block, true_exprt{}));
    step_instrs.destructive_append(havoc_instrs);
    step_instrs.add(
      goto_programt::make_assignment(in_loop_havoc_block, false_exprt{}));
  }

  goto_convertt converter(symbol_table, log.get_message_handler());
  {
    // Assume the loop invariant after havocing the state.
    code_assumet assumption{invariant};
    assumption.add_source_location() = loop_head_location;
    converter.goto_convert(assumption, step_instrs, language_mode);
  }

  {
    // Generate assignments to store the multidimensional decreases clause's
    // value just before the loop_head.
    for(size_t i = 0; i < old_decreases_vars.size(); i++)
    {
      code_frontend_assignt old_decreases_assignment{
        old_decreases_vars[i], decreases_clauses[i], loop_head_location};
      converter.goto_convert(
        old_decreases_assignment, step_instrs, language_mode);
    }
  }

  goto_function.body.destructive_insert(loop_head, step_instrs);

  return step_case_target;
}

void dfcc_instrument_loopt::add_body_instructions(
  const std::size_t loop_id,
  const std::size_t cbmc_loop_id,
  goto_functionst::goto_functiont &goto_function,
  symbol_tablet &symbol_table,
  goto_programt::targett loop_head,
  goto_programt::targett loop_latch,
  const exprt &invariant,
  const exprt::operandst &decreases_clauses,
  const symbol_exprt &entered_loop,
  const symbol_exprt &in_base_case,
  const std::vector<symbol_exprt> &old_decreases_vars,
  const std::vector<symbol_exprt> &new_decreases_vars,
  const goto_programt::instructiont::targett &step_case_target,
  const irep_idt &language_mode)
{
  auto loop_head_location(loop_head->source_location());
  dfcc_remove_loop_tags(loop_head_location);

  // HEAD: // Loop body block
  //   ... eval guard ...
  //   IF (!guard) GOTO EXIT;
  //   ... loop body ...
  //   // instrumentation
  //   entered_loop = true
  //   // Jump back to the step case if the loop can run at least once
  //   IF (in_base_case) GOTO STEP;
  //   ASSERT(<loop_invariant>);
  //    new_variant = <loop_decreases>;
  //   ASSERT(new_variant < old_variant);
  //   ASSUME(false);

  goto_programt pre_loop_latch_instrs;

  {
    // Record that we entered the loop with `entered_loop = true`.
    pre_loop_latch_instrs.add(
      goto_programt::make_assignment(entered_loop, true_exprt{}));
  }

  {
    // Jump back to the step case to havoc the write set, assume the invariant,
    // and execute an arbitrary iteration.
    pre_loop_latch_instrs.add(goto_programt::make_goto(
      step_case_target, in_base_case, loop_head_location));
  }

  goto_convertt converter(symbol_table, log.get_message_handler());
  {
    // Because of the unconditional jump above the following code is only
    // reachable in the step case. Generate the inductive invariant check
    // `ASSERT(invariant)`.
    source_locationt check_location(loop_head_location);
    check_location.set_property_class("loop_invariant_step");
    check_location.set_comment(
      "Check invariant after step for loop " +
      id2string(check_location.get_function()) + "." +
      std::to_string(cbmc_loop_id));
    code_assertt assertion{invariant};
    assertion.add_source_location() = check_location;
    converter.goto_convert(assertion, pre_loop_latch_instrs, language_mode);
  }

  {
    // Generate assignments to store the multidimensional decreases clause's
    // value after one iteration of the loop.
    if(!decreases_clauses.empty())
    {
      for(size_t i = 0; i < new_decreases_vars.size(); i++)
      {
        code_frontend_assignt new_decreases_assignment{
          new_decreases_vars[i], decreases_clauses[i], loop_head_location};
        converter.goto_convert(
          new_decreases_assignment, pre_loop_latch_instrs, language_mode);
      }

      // Generate assertion that the multidimensional decreases clause's value
      // after the loop is lexicographically smaller than its initial value.
      source_locationt check_location(loop_head_location);
      check_location.set_property_class("loop_decreases");
      check_location.set_comment(
        "Check variant decreases after step for loop " +
        id2string(check_location.get_function()) + "." +
        std::to_string(cbmc_loop_id));
      pre_loop_latch_instrs.add(goto_programt::make_assertion(
        generate_lexicographic_less_than_check(
          new_decreases_vars, old_decreases_vars),
        check_location));

      // Discard the temporary variables that store decreases clause's value.
      for(size_t i = 0; i < old_decreases_vars.size(); i++)
      {
        pre_loop_latch_instrs.add(
          goto_programt::make_dead(old_decreases_vars[i], loop_head_location));
        pre_loop_latch_instrs.add(
          goto_programt::make_dead(new_decreases_vars[i], loop_head_location));
      }
    }
  }

  insert_before_swap_and_advance(
    goto_function.body, loop_latch, pre_loop_latch_instrs);

  {
    // Change the back edge into assume(false) or assume(!guard).
    loop_latch->turn_into_assume();
    loop_latch->condition_nonconst() = boolean_negate(loop_latch->condition());
  }
}

void dfcc_instrument_loopt::add_exit_instructions(
  const std::size_t loop_id,
  const std::size_t cbmc_loop_id,
  goto_functionst::goto_functiont &goto_function,
  goto_programt::targett loop_head,
  const symbol_exprt &loop_write_set,
  const symbol_exprt &addr_of_loop_write_set,
  const std::map<exprt, exprt> &history_var_map,
  const symbol_exprt &entered_loop,
  const symbol_exprt &initial_invariant,
  const symbol_exprt &in_base_case,
  const std::vector<symbol_exprt> &old_decreases_vars,
  const std::vector<symbol_exprt> &new_decreases_vars)
{
  // Collect all exit targets of the loop.
  std::set<goto_programt::targett> exit_targets;

  for(goto_programt::instructiont::targett target =
        goto_function.body.instructions.begin();
      target != goto_function.body.instructions.end();
      target++)
  {
    if(!dfcc_is_loop_exiting(target) || !dfcc_has_loop_id(target, loop_id))
      continue;
    INVARIANT(target->is_goto(), "Exiting instructions must be GOTOs");
    auto exit_target = target->get_target();
    auto exit_loop_id_opt = dfcc_get_loop_id(exit_target);
    INVARIANT(
      exit_loop_id_opt.has_value() && exit_loop_id_opt.value() != loop_id,
      "Exiting instructions must jump out of the loop");
    exit_targets.insert(exit_target);
  }

  // For each exit target of the loop, insert a code block:
  // ```
  // EXIT:
  //   // check that step case was checked if loop can run once
  //   ASSUME (entered_loop ==> !in_base_case);
  //   DEAD loop_entry history vars, in_base_case;
  //   DEAD initial_invariant, entered_loop;
  //   DEAD old_variant, in_loop_havoc_block;
  //   __write_set_release(w_loop);
  //   DEAD __ws_loop, ws_loop;
  // ```

  for(auto exit_target : exit_targets)
  {
    goto_programt loop_exit_program;

    // Use the head location for this check as well so that all checks related
    // to a given loop are presented as coming from the loop head.
    source_locationt check_location = loop_head->source_location();
    check_location.set_property_class("loop_step_unwinding");
    check_location.set_comment(
      "Check step was unwound for loop " +
      id2string(check_location.get_function()) + "." +
      std::to_string(cbmc_loop_id));
    loop_exit_program.add(goto_programt::make_assertion(
      or_exprt{not_exprt{entered_loop}, not_exprt{in_base_case}},
      check_location));

    // Mark instrumentation variables as going out of scope.
    const source_locationt &exit_location = exit_target->source_location();
    loop_exit_program.add(
      goto_programt::make_dead(in_base_case, exit_location));
    loop_exit_program.add(
      goto_programt::make_dead(entered_loop, exit_location));
    loop_exit_program.add(
      goto_programt::make_dead(initial_invariant, exit_location));

    // Release the write set resources.
    loop_exit_program.add(goto_programt::make_function_call(
      library.write_set_release_call(addr_of_loop_write_set, exit_location),
      exit_location));

    // Mark write set as going out of scope.
    loop_exit_program.add(
      goto_programt::make_dead(to_symbol_expr(loop_write_set), exit_location));
    loop_exit_program.add(goto_programt::make_dead(
      to_symbol_expr(addr_of_loop_write_set), exit_location));

    // Mark history variables as going out of scope.
    for(const auto &v : history_var_map)
    {
      loop_exit_program.add(
        goto_programt::make_dead(to_symbol_expr(v.second), exit_location));
    }

    // Mark decreases clause snapshots as gong out of scope.
    for(size_t i = 0; i < old_decreases_vars.size(); i++)
    {
      loop_exit_program.add(
        goto_programt::make_dead(old_decreases_vars[i], exit_location));
      loop_exit_program.add(
        goto_programt::make_dead(new_decreases_vars[i], exit_location));
    }

    // Insert the exit block, preserving the loop end target.
    insert_before_swap_and_advance(
      goto_function.body, exit_target, loop_exit_program);
  }
}
