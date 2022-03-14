/*******************************************************************\

Module: Verify and use annotated loop and function contracts

Author: Michael Tautschnig

Date: February 2016

\*******************************************************************/

/// \file
/// Verify and use annotated loop and function contracts

#include "contracts.h"

#include <algorithm>
#include <map>

#include <analyses/local_bitvector_analysis.h>
#include <analyses/local_may_alias.h>

#include <ansi-c/c_expr.h>

#include <goto-instrument/havoc_utils.h>

#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_program.h>
#include <goto-programs/remove_skip.h>

#include <langapi/language_util.h>

#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/format_expr.h>
#include <util/fresh_symbol.h>
#include <util/graph.h>
#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>
#include <util/message.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/replace_symbol.h>
#include <util/std_code.h>

#include "havoc_assigns_clause_targets.h"
#include "instrument_spec_assigns.h"
#include "memory_predicates.h"
#include "utils.h"

/// Decorator for \ref message_handlert that keeps track of warnings
/// occuring when inlining a function.
///
/// It counts the number of :
/// - recursive functions warnings
/// - missing functions warnings
/// - missing function body warnings
/// - missing function arguments warnings
class inlining_decoratort : public message_handlert
{
private:
  message_handlert &wrapped;
  unsigned int recursive_function_warnings_count = 0;

  void parse_message(const std::string &message)
  {
    if(message.find("recursion is ignored on call") != std::string::npos)
      recursive_function_warnings_count++;
  }

public:
  explicit inlining_decoratort(message_handlert &_wrapped) : wrapped(_wrapped)
  {
  }

  unsigned int get_recursive_function_warnings_count()
  {
    return recursive_function_warnings_count;
  }

  void print(unsigned level, const std::string &message) override
  {
    parse_message(message);
    wrapped.print(level, message);
  }

  void print(unsigned level, const xmlt &xml) override
  {
    wrapped.print(level, xml);
  }

  void print(unsigned level, const jsont &json) override
  {
    wrapped.print(level, json);
  }

  void print(unsigned level, const structured_datat &data) override
  {
    wrapped.print(level, data);
  }

  void print(
    unsigned level,
    const std::string &message,
    const source_locationt &location) override
  {
    parse_message(message);
    wrapped.print(level, message, location);
    return;
  }

  void flush(unsigned i) override
  {
    return wrapped.flush(i);
  }

  void set_verbosity(unsigned _verbosity)
  {
    wrapped.set_verbosity(_verbosity);
  }

  unsigned get_verbosity() const
  {
    return wrapped.get_verbosity();
  }

  std::size_t get_message_count(unsigned level) const
  {
    return wrapped.get_message_count(level);
  }

  std::string command(unsigned i) const override
  {
    return wrapped.command(i);
  }
};

void code_contractst::check_apply_loop_contracts(
  const irep_idt &function_name,
  goto_functionst::goto_functiont &goto_function,
  const local_may_aliast &local_may_alias,
  goto_programt::targett loop_head,
  goto_programt::targett loop_end,
  const loopt &loop,
  exprt assigns_clause,
  exprt invariant,
  exprt decreases_clause,
  const irep_idt &mode)
{
  const auto loop_head_location = loop_head->source_location();

  // Vector representing a (possibly multidimensional) decreases clause
  const auto &decreases_clause_exprs = decreases_clause.operands();

  // Temporary variables for storing the multidimensional decreases clause
  // at the start of and end of a loop body
  std::vector<symbol_exprt> old_decreases_vars, new_decreases_vars;

  replace_symbolt replace;
  code_contractst::add_quantified_variable(invariant, replace, mode);
  replace(invariant);

  // instrument
  //
  //   ... preamble ...
  // HEAD:
  //   ... eval guard ...
  //   if (!guard)
  //     goto EXIT;
  //   ... loop body ...
  //   goto HEAD;
  // EXIT:
  //   ... postamble ...
  //
  // to
  //
  //                               ... preamble ...
  //                        ,-     initialize loop_entry history vars;
  //                        |      entered_loop = false
  // loop assigns check     |      initial_invariant_val = invariant_expr;
  //  - unchecked, temps    |      in_base_case = true;
  // func assigns check     |      snapshot (write_set);
  //  - disabled via pragma |      goto HEAD;
  //                        |    STEP:
  //                  --.   |      assert (initial_invariant_val);
  // loop assigns check |   |      in_base_case = false;
  //  - not applicable   >=======  havoc (assigns_set);
  // func assigns check |   |      assume (invariant_expr);
  //  + deferred        |   `-     old_variant_val = decreases_clause_expr;
  //                  --'      * HEAD:
  // loop assigns check     ,-     ... eval guard ...
  //  + assertions added    |      if (!guard)
  // func assigns check     |        goto EXIT;
  //  - disabled via pragma `-     ... loop body ...
  //                        ,-     entered_loop = true
  //                        |      if (in_base_case)
  //                        |        goto STEP;
  // loop assigns check     |      assert (invariant_expr);
  //  - unchecked, temps    |      new_variant_val = decreases_clause_expr;
  // func assigns check     |      assert (new_variant_val < old_variant_val);
  //  - disabled via pragma |      dead old_variant_val, new_variant_val;
  //                        |  *   assume (false);
  //                        |  * EXIT:
  // To be inserted at  ,~~~|~~~~  assert (entered_loop ==> !in_base_case);
  // every unique EXIT  |   |      dead loop_entry history vars, in_base_case;
  // (break, goto etc.) `~~~`- ~~  dead initial_invariant_val, entered_loop;
  //                               ... postamble ..
  //
  // Asterisks (*) denote anchor points (goto targets) for instrumentations.
  // We insert generated code above and/below these targets.
  //
  // Assertions for assigns clause checking are inserted in the loop body.

  // an intermediate goto_program to store generated instructions
  // to be inserted before the loop head
  goto_programt pre_loop_head_instrs;

  // Process "loop_entry" history variables.
  // We find and replace all "__CPROVER_loop_entry" subexpressions in invariant.
  std::map<exprt, exprt> history_var_map;
  replace_history_parameter(
    invariant,
    history_var_map,
    loop_head_location,
    mode,
    pre_loop_head_instrs,
    ID_loop_entry);

  // Create a temporary to track if we entered the loop,
  // i.e., the loop guard was satisfied.
  const auto entered_loop =
    new_tmp_symbol(
      bool_typet(), loop_head_location, mode, symbol_table, "__entered_loop")
      .symbol_expr();
  pre_loop_head_instrs.add(
    goto_programt::make_decl(entered_loop, loop_head_location));
  pre_loop_head_instrs.add(
    goto_programt::make_assignment(entered_loop, false_exprt{}));

  // Create a snapshot of the invariant so that we can check the base case,
  // if the loop is not vacuous and must be abstracted with contracts.
  const auto initial_invariant_val =
    new_tmp_symbol(
      bool_typet(), loop_head_location, mode, symbol_table, "__init_invariant")
      .symbol_expr();
  pre_loop_head_instrs.add(
    goto_programt::make_decl(initial_invariant_val, loop_head_location));
  {
    // Although the invariant at this point will not have side effects,
    // it is still a C expression, and needs to be "goto_convert"ed.
    // Note that this conversion may emit many GOTO instructions.
    code_assignt initial_invariant_value_assignment{
      initial_invariant_val, invariant};
    initial_invariant_value_assignment.add_source_location() =
      loop_head_location;
    converter.goto_convert(
      initial_invariant_value_assignment, pre_loop_head_instrs, mode);
  }

  // Create a temporary variable to track base case vs inductive case
  // instrumentation of the loop.
  const auto in_base_case =
    new_tmp_symbol(
      bool_typet(), loop_head_location, mode, symbol_table, "__in_base_case")
      .symbol_expr();
  pre_loop_head_instrs.add(
    goto_programt::make_decl(in_base_case, loop_head_location));
  pre_loop_head_instrs.add(
    goto_programt::make_assignment(in_base_case, true_exprt{}));

  // CAR snapshot instructions for checking assigns clause
  goto_programt snapshot_instructions;

  // track static local symbols
  instrument_spec_assignst instrument_spec_assigns(
    function_name, goto_functions, symbol_table, log.get_message_handler());
  instrument_spec_assigns.track_static_locals_between(
    loop_head, loop_end, snapshot_instructions);

  // set of targets to havoc
  assignst to_havoc;

  if(assigns_clause.is_nil())
  {
    // No assigns clause was specified for this loop.
    // Infer memory locations assigned by the loop from the loop instructions
    // and the inferred aliasing relation.
    try
    {
      get_assigns(local_may_alias, loop, to_havoc);
      // TODO: if the set contains pairs (i, a[i]),
      // we must at least widen them to (i, pointer_object(a))

      log.debug() << "No loop assigns clause provided. Inferred targets: {";
      // Add inferred targets to the loop assigns clause.
      bool ran_once = false;
      for(const auto &target : to_havoc)
      {
        if(ran_once)
          log.debug() << ", ";
        ran_once = true;
        log.debug() << format(target);
        instrument_spec_assigns.track_spec_target(
          target, snapshot_instructions);
      }
      log.debug() << "}" << messaget::eom;

      instrument_spec_assigns.get_static_locals(
        std::inserter(to_havoc, to_havoc.end()));
    }
    catch(const analysis_exceptiont &exc)
    {
      log.error() << "Failed to infer variables being modified by the loop at "
                  << loop_head_location
                  << ".\nPlease specify an assigns clause.\nReason:"
                  << messaget::eom;
      throw exc;
    }
  }
  else
  {
    // An assigns clause was specified for this loop.
    // Add the targets to the set of expressions to havoc.
    for(const auto &target : assigns_clause.operands())
    {
      to_havoc.insert(target);
      instrument_spec_assigns.track_spec_target(target, snapshot_instructions);
    }
  }

  // Insert instrumentation
  // This must be done before havocing the write set.
  // FIXME: this is not true for write set targets that
  // might depend on other write set targets.
  pre_loop_head_instrs.destructive_append(snapshot_instructions);

  // Insert a jump to the loop head
  // (skipping over the step case initialization code below)
  pre_loop_head_instrs.add(
    goto_programt::make_goto(loop_head, true_exprt{}, loop_head_location));

  // The STEP case instructions follow.
  // We skip past it initially, because of the unconditional jump above,
  // but jump back here if we get past the loop guard while in_base_case.

  const auto step_case_target =
    pre_loop_head_instrs.add(goto_programt::make_assignment(
      in_base_case, false_exprt{}, loop_head_location));

  // If we jump here, then the loop runs at least once,
  // so add the base case assertion:
  //   assert(initial_invariant_val)
  // We use a block scope for assertion, since it's immediately goto converted,
  // and doesn't need to be kept around.
  {
    code_assertt assertion{initial_invariant_val};
    assertion.add_source_location() = loop_head_location;
    converter.goto_convert(assertion, pre_loop_head_instrs, mode);
    pre_loop_head_instrs.instructions.back()
      .source_location_nonconst()
      .set_comment("Check loop invariant before entry");
  }

  // Insert the first block of pre_loop_head_instrs,
  // with a pragma to disable assigns clause checking.
  // All of the initialization code so far introduces local temporaries,
  // which need not be checked against the enclosing scope's assigns clause.
  goto_function.body.destructive_insert(
    loop_head, add_pragma_disable_assigns_check(pre_loop_head_instrs));

  // Generate havocing code for assignment targets.
  havoc_assigns_targetst havoc_gen(to_havoc, ns);
  havoc_gen.append_full_havoc_code(loop_head_location, pre_loop_head_instrs);

  // Insert the second block of pre_loop_head_instrs: the havocing code.
  // We do not `add_pragma_disable_assigns_check`,
  // so that the enclosing scope's assigns clause instrumentation
  // would pick these havocs up for inclusion (subset) checks.
  goto_function.body.destructive_insert(loop_head, pre_loop_head_instrs);

  // Generate: assume(invariant) just after havocing
  // We use a block scope for assumption, since it's immediately goto converted,
  // and doesn't need to be kept around.
  {
    code_assumet assumption{invariant};
    assumption.add_source_location() = loop_head_location;
    converter.goto_convert(assumption, pre_loop_head_instrs, mode);
  }

  // Create fresh temporary variables that store the multidimensional
  // decreases clause's value before and after the loop
  for(const auto &clause : decreases_clause.operands())
  {
    const auto old_decreases_var =
      new_tmp_symbol(clause.type(), loop_head_location, mode, symbol_table)
        .symbol_expr();
    pre_loop_head_instrs.add(
      goto_programt::make_decl(old_decreases_var, loop_head_location));
    old_decreases_vars.push_back(old_decreases_var);

    const auto new_decreases_var =
      new_tmp_symbol(clause.type(), loop_head_location, mode, symbol_table)
        .symbol_expr();
    pre_loop_head_instrs.add(
      goto_programt::make_decl(new_decreases_var, loop_head_location));
    new_decreases_vars.push_back(new_decreases_var);
  }

  // TODO: Fix loop contract handling for do/while loops.
  if(loop_end->is_goto() && !loop_end->get_condition().is_true())
  {
    log.error() << "Loop contracts are unsupported on do/while loops: "
                << loop_head_location << messaget::eom;
    throw 0;

    // non-deterministically skip the loop if it is a do-while loop.
    // pre_loop_head_instrs.add(goto_programt::make_goto(
    //   loop_end, side_effect_expr_nondett(bool_typet(), loop_head_location)));
  }

  // Generate: assignments to store the multidimensional decreases clause's
  // value just before the loop_head
  if(!decreases_clause.is_nil())
  {
    for(size_t i = 0; i < old_decreases_vars.size(); i++)
    {
      code_assignt old_decreases_assignment{
        old_decreases_vars[i], decreases_clause_exprs[i]};
      old_decreases_assignment.add_source_location() = loop_head_location;
      converter.goto_convert(
        old_decreases_assignment, pre_loop_head_instrs, mode);
    }

    goto_function.body.destructive_insert(
      loop_head, add_pragma_disable_assigns_check(pre_loop_head_instrs));
  }

  // Insert the third and final block of pre_loop_head_instrs,
  // with a pragma to disable assigns clause checking.
  // The variables to store old variant value are local temporaries,
  // which need not be checked against the enclosing scope's assigns clause.
  goto_function.body.destructive_insert(
    loop_head, add_pragma_disable_assigns_check(pre_loop_head_instrs));

  optionalt<cfg_infot> cfg_empty_info;

  // Perform write set instrumentation on the entire loop.
  instrument_spec_assigns.instrument_instructions(
    goto_function.body,
    loop_head,
    loop_end,
    skip_function_paramst::NO,
    // do not use CFG info for now
    cfg_empty_info);

  // Now we begin instrumenting at the loop_end.
  // `pre_loop_end_instrs` are to be inserted before `loop_end`.
  goto_programt pre_loop_end_instrs;

  // Record that we entered the loop.
  pre_loop_end_instrs.add(
    goto_programt::make_assignment(entered_loop, true_exprt{}));

  // Jump back to the step case to havoc the write set, assume the invariant,
  // and execute an arbitrary iteration.
  pre_loop_end_instrs.add(goto_programt::make_goto(
    step_case_target, in_base_case, loop_head_location));

  // The following code is only reachable in the step case,
  // i.e., when in_base_case == false,
  // because of the unconditional jump above.

  // Generate the inductiveness check:
  //   assert(invariant)
  // We use a block scope for assertion, since it's immediately goto converted,
  // and doesn't need to be kept around.
  {
    code_assertt assertion{invariant};
    assertion.add_source_location() = loop_head_location;
    converter.goto_convert(assertion, pre_loop_end_instrs, mode);
    pre_loop_end_instrs.instructions.back()
      .source_location_nonconst()
      .set_comment("Check that loop invariant is preserved");
  }

  // Generate: assignments to store the multidimensional decreases clause's
  // value after one iteration of the loop
  if(!decreases_clause.is_nil())
  {
    for(size_t i = 0; i < new_decreases_vars.size(); i++)
    {
      code_assignt new_decreases_assignment{
        new_decreases_vars[i], decreases_clause_exprs[i]};
      new_decreases_assignment.add_source_location() = loop_head_location;
      converter.goto_convert(
        new_decreases_assignment, pre_loop_end_instrs, mode);
    }

    // Generate: assertion that the multidimensional decreases clause's value
    // after the loop is lexicographically smaller than its initial value.
    code_assertt monotonic_decreasing_assertion{
      generate_lexicographic_less_than_check(
        new_decreases_vars, old_decreases_vars)};
    monotonic_decreasing_assertion.add_source_location() = loop_head_location;
    converter.goto_convert(
      monotonic_decreasing_assertion, pre_loop_end_instrs, mode);
    pre_loop_end_instrs.instructions.back()
      .source_location_nonconst()
      .set_comment("Check decreases clause on loop iteration");

    // Discard the temporary variables that store decreases clause's value
    for(size_t i = 0; i < old_decreases_vars.size(); i++)
    {
      pre_loop_end_instrs.add(
        goto_programt::make_dead(old_decreases_vars[i], loop_head_location));
      pre_loop_end_instrs.add(
        goto_programt::make_dead(new_decreases_vars[i], loop_head_location));
    }
  }

  insert_before_swap_and_advance(
    goto_function.body,
    loop_end,
    add_pragma_disable_assigns_check(pre_loop_end_instrs));

  // change the back edge into assume(false) or assume(guard)
  loop_end->turn_into_assume();
  loop_end->set_condition(boolean_negate(loop_end->get_condition()));

  std::set<goto_programt::targett> seen_targets;
  // Find all exit points of the loop, make temporary variables `DEAD`,
  // and check that step case was checked for non-vacuous loops.
  for(const auto &t : loop)
  {
    if(!t->is_goto())
      continue;

    auto exit_target = t->get_target();
    if(
      loop.contains(exit_target) ||
      seen_targets.find(exit_target) != seen_targets.end())
      continue;

    seen_targets.insert(exit_target);

    goto_programt pre_loop_exit_instrs;
    // Assertion to check that step case was checked if we entered the loop.
    pre_loop_exit_instrs.add(goto_programt::make_assertion(
      or_exprt{not_exprt{entered_loop}, not_exprt{in_base_case}},
      loop_head_location));
    pre_loop_exit_instrs.instructions.back()
      .source_location_nonconst()
      .set_comment("Check that loop instrumentation was not truncated");
    // Instructions to make all the temporaries go dead.
    pre_loop_exit_instrs.add(
      goto_programt::make_dead(in_base_case, loop_head_location));
    pre_loop_exit_instrs.add(
      goto_programt::make_dead(initial_invariant_val, loop_head_location));
    for(const auto &v : history_var_map)
    {
      pre_loop_exit_instrs.add(
        goto_programt::make_dead(to_symbol_expr(v.second), loop_head_location));
    }
    // Insert these instructions, preserving the loop end target.
    insert_before_swap_and_advance(
      goto_function.body, exit_target, pre_loop_exit_instrs);
  }
}

void code_contractst::add_quantified_variable(
  const exprt &expression,
  replace_symbolt &replace,
  const irep_idt &mode)
{
  if(expression.id() == ID_not || expression.id() == ID_typecast)
  {
    // For unary connectives, recursively check for
    // nested quantified formulae in the term
    const auto &unary_expression = to_unary_expr(expression);
    add_quantified_variable(unary_expression.op(), replace, mode);
  }
  if(expression.id() == ID_notequal || expression.id() == ID_implies)
  {
    // For binary connectives, recursively check for
    // nested quantified formulae in the left and right terms
    const auto &binary_expression = to_binary_expr(expression);
    add_quantified_variable(binary_expression.lhs(), replace, mode);
    add_quantified_variable(binary_expression.rhs(), replace, mode);
  }
  if(expression.id() == ID_if)
  {
    // For ternary connectives, recursively check for
    // nested quantified formulae in all three terms
    const auto &if_expression = to_if_expr(expression);
    add_quantified_variable(if_expression.cond(), replace, mode);
    add_quantified_variable(if_expression.true_case(), replace, mode);
    add_quantified_variable(if_expression.false_case(), replace, mode);
  }
  if(expression.id() == ID_and || expression.id() == ID_or)
  {
    // For multi-ary connectives, recursively check for
    // nested quantified formulae in all terms
    const auto &multi_ary_expression = to_multi_ary_expr(expression);
    for(const auto &operand : multi_ary_expression.operands())
    {
      add_quantified_variable(operand, replace, mode);
    }
  }
  else if(expression.id() == ID_exists || expression.id() == ID_forall)
  {
    // When a quantifier expression is found,
    // for each quantified variable ...
    const auto &quantifier_expression = to_quantifier_expr(expression);
    for(const auto &quantified_variable : quantifier_expression.variables())
    {
      const auto &quantified_symbol = to_symbol_expr(quantified_variable);

      // 1. create fresh symbol
      symbolt new_symbol = new_tmp_symbol(
        quantified_symbol.type(),
        quantified_symbol.source_location(),
        mode,
        symbol_table);

      // 2. add created fresh symbol to expression map
      symbol_exprt q(
        quantified_symbol.get_identifier(), quantified_symbol.type());
      replace.insert(q, new_symbol.symbol_expr());

      // 3. recursively check for nested quantified formulae
      add_quantified_variable(quantifier_expression.where(), replace, mode);
    }
  }
}

void code_contractst::replace_history_parameter(
  exprt &expr,
  std::map<exprt, exprt> &parameter2history,
  source_locationt location,
  const irep_idt &mode,
  goto_programt &history,
  const irep_idt &id)
{
  for(auto &op : expr.operands())
  {
    replace_history_parameter(
      op, parameter2history, location, mode, history, id);
  }

  if(expr.id() == ID_old || expr.id() == ID_loop_entry)
  {
    const auto &parameter = to_history_expr(expr, id).expression();

    const auto &id = parameter.id();
    if(
      id == ID_dereference || id == ID_member || id == ID_symbol ||
      id == ID_ptrmember || id == ID_constant || id == ID_typecast)
    {
      auto it = parameter2history.find(parameter);

      if(it == parameter2history.end())
      {
        // 0. Create a skip target to jump to, if the parameter is invalid
        goto_programt skip_program;
        const auto skip_target =
          skip_program.add(goto_programt::make_skip(location));

        // 1. Create a temporary symbol expression that represents the
        // history variable
        symbol_exprt tmp_symbol =
          new_tmp_symbol(parameter.type(), location, mode, symbol_table)
            .symbol_expr();

        // 2. Associate the above temporary variable to it's corresponding
        // expression
        parameter2history[parameter] = tmp_symbol;

        // 3. Add the required instructions to the instructions list
        // 3.1. Declare the newly created temporary variable
        history.add(goto_programt::make_decl(tmp_symbol, location));

        // 3.2. Skip storing the history if the expression is invalid
        history.add(goto_programt::make_goto(
          skip_target,
          not_exprt{all_dereferences_are_valid(parameter, ns)},
          location));

        // 3.3. Add an assignment such that the value pointed to by the new
        // temporary variable is equal to the value of the corresponding
        // parameter
        history.add(
          goto_programt::make_assignment(tmp_symbol, parameter, location));

        // 3.4. Add a skip target
        history.destructive_append(skip_program);
      }

      expr = parameter2history[parameter];
    }
    else
    {
      log.error() << "Tracking history of " << parameter.id()
                  << " expressions is not supported yet." << messaget::eom;
      throw 0;
    }
  }
}

std::pair<goto_programt, goto_programt>
code_contractst::create_ensures_instruction(
  codet &expression,
  source_locationt location,
  const irep_idt &mode)
{
  std::map<exprt, exprt> parameter2history;
  goto_programt history;

  // Find and replace "old" expression in the "expression" variable
  replace_history_parameter(
    expression, parameter2history, location, mode, history, ID_old);

  // Create instructions corresponding to the ensures clause
  goto_programt ensures_program;
  converter.goto_convert(expression, ensures_program, mode);

  // return a pair containing:
  // 1. instructions corresponding to the ensures clause
  // 2. instructions related to initializing the history variables
  return std::make_pair(std::move(ensures_program), std::move(history));
}

bool code_contractst::apply_function_contract(
  const irep_idt &function,
  const source_locationt &location,
  goto_programt &function_body,
  goto_programt::targett &target)
{
  const auto &const_target =
    static_cast<const goto_programt::targett &>(target);
  // Return if the function is not named in the call; currently we don't handle
  // function pointers.
  PRECONDITION(const_target->call_function().id() == ID_symbol);

  // Retrieve the function type, which is needed to extract the contract
  // components.
  const irep_idt &target_function =
    to_symbol_expr(const_target->call_function()).get_identifier();
  const symbolt &function_symbol = ns.lookup(target_function);
  const auto &type = to_code_with_contract_type(function_symbol.type);

  // Isolate each component of the contract.
  auto assigns_clause = type.assigns();
  auto requires = conjunction(type.requires());
  auto ensures = conjunction(type.ensures());

  // Create a replace_symbolt object, for replacing expressions in the callee
  // with expressions from the call site (e.g. the return value).
  // This object tracks replacements that are common to ENSURES and REQUIRES.
  replace_symbolt common_replace;

  // keep track of the call's return expression to make it nondet later
  optionalt<exprt> call_ret_opt = {};

  // if true, the call return variable variable was created during replacement
  bool call_ret_is_fresh_var = false;

  if(type.return_type() != empty_typet())
  {
    // Check whether the function's return value is not disregarded.
    if(target->call_lhs().is_not_nil())
    {
      // If so, have it replaced appropriately.
      // For example, if foo() ensures that its return value is > 5, then
      // rewrite calls to foo as follows:
      // x = foo() -> assume(__CPROVER_return_value > 5) -> assume(x > 5)
      auto &lhs_expr = const_target->call_lhs();
      call_ret_opt = lhs_expr;
      symbol_exprt ret_val(CPROVER_PREFIX "return_value", lhs_expr.type());
      common_replace.insert(ret_val, lhs_expr);
    }
    else
    {
      // If the function does return a value, but the return value is
      // disregarded, check if the postcondition includes the return value.
      return_value_visitort v;
      ensures.visit(v);
      if(v.found_return_value())
      {
        // The postcondition does mention __CPROVER_return_value, so mint a
        // fresh variable to replace __CPROVER_return_value with.
        call_ret_is_fresh_var = true;
        const symbolt &fresh = get_fresh_aux_symbol(
          type.return_type(),
          id2string(target_function),
          "ignored_return_value",
          const_target->source_location(),
          symbol_table.lookup_ref(target_function).mode,
          ns,
          symbol_table);
        symbol_exprt ret_val(CPROVER_PREFIX "return_value", type.return_type());
        auto fresh_sym_expr = fresh.symbol_expr();
        common_replace.insert(ret_val, fresh_sym_expr);
        call_ret_opt = fresh_sym_expr;
      }
    }
  }

  // Replace formal parameters
  const auto &arguments = const_target->call_arguments();
  auto a_it = arguments.begin();
  for(auto p_it = type.parameters().begin();
      p_it != type.parameters().end() && a_it != arguments.end();
      ++p_it, ++a_it)
  {
    if(!p_it->get_identifier().empty())
    {
      symbol_exprt p(p_it->get_identifier(), p_it->type());
      common_replace.insert(p, *a_it);
    }
  }

  const auto &mode = symbol_table.lookup_ref(target_function).mode;

  is_fresh_replacet is_fresh(*this, log, target_function);
  is_fresh.create_declarations();

  // Insert assertion of the precondition immediately before the call site.
  if(!requires.is_true())
  {
    replace_symbolt replace(common_replace);
    code_contractst::add_quantified_variable(requires, replace, mode);
    replace(requires);

    goto_programt assertion;
    converter.goto_convert(
      code_assertt(requires),
      assertion,
      symbol_table.lookup_ref(target_function).mode);
    assertion.instructions.back().source_location_nonconst() =
      requires.source_location();
    assertion.instructions.back().source_location_nonconst().set_comment(
      "Check requires clause");
    assertion.instructions.back().source_location_nonconst().set_property_class(
      ID_precondition);
    is_fresh.update_requires(assertion);
    insert_before_swap_and_advance(function_body, target, assertion);
  }

  // Gather all the instructions required to handle history variables
  // as well as the ensures clause
  std::pair<goto_programt, goto_programt> ensures_pair;
  if(!ensures.is_false())
  {
    replace_symbolt replace(common_replace);
    code_contractst::add_quantified_variable(ensures, replace, mode);
    replace(ensures);

    auto assumption = code_assumet(ensures);
    ensures_pair = create_ensures_instruction(
      assumption,
      ensures.source_location(),
      symbol_table.lookup_ref(target_function).mode);

    // add all the history variable initialization instructions
    // to the goto program
    insert_before_swap_and_advance(function_body, target, ensures_pair.second);
  }

  // ASSIGNS clause should not refer to any quantified variables,
  // and only refer to the common symbols to be replaced.
  exprt targets;
  for(auto &target : assigns_clause)
    targets.add_to_operands(std::move(target));
  common_replace(targets);

  // Create a sequence of non-deterministic assignments ...

  // ... for the assigns clause targets and static locals
  goto_programt havoc_instructions;

  havoc_assigns_clause_targetst havocker(
    target_function,
    targets.operands(),
    goto_functions,
    location,
    symbol_table,
    log.get_message_handler());

  havocker.get_instructions(havoc_instructions);

  // ... for the return value
  if(call_ret_opt.has_value())
  {
    auto &call_ret = call_ret_opt.value();
    auto &loc = call_ret.source_location();
    auto &type = call_ret.type();

    // Declare if fresh
    if(call_ret_is_fresh_var)
      havoc_instructions.add(
        goto_programt::make_decl(to_symbol_expr(call_ret), loc));

    side_effect_expr_nondett expr(type, location);
    auto target = havoc_instructions.add(
      goto_programt::make_assignment(call_ret, expr, loc));
    target->code_nonconst().add_source_location() = loc;
  }

  // Insert havoc instructions immediately before the call site.
  insert_before_swap_and_advance(function_body, target, havoc_instructions);

  // To remove the function call, insert statements related to the assumption.
  // Then, replace the function call with a SKIP statement.
  if(!ensures.is_false())
  {
    is_fresh.update_ensures(ensures_pair.first);
    insert_before_swap_and_advance(function_body, target, ensures_pair.first);
  }

  // Kill return value variable if fresh
  if(call_ret_is_fresh_var)
  {
    function_body.output_instruction(ns, "", log.warning(), *target);
    auto dead_inst =
      goto_programt::make_dead(to_symbol_expr(call_ret_opt.value()), location);
    function_body.insert_before_swap(target, dead_inst);
    ++target;
  }

  // Erase original function call
  *target = goto_programt::make_skip();

  // Add this function to the set of replaced functions.
  summarized.insert(target_function);
  return false;
}

void code_contractst::apply_loop_contract(
  const irep_idt &function_name,
  goto_functionst::goto_functiont &goto_function)
{
  const bool may_have_loops = std::any_of(
    goto_function.body.instructions.begin(),
    goto_function.body.instructions.end(),
    [](const goto_programt::instructiont &instruction) {
      return instruction.is_backwards_goto();
    });

  if(!may_have_loops)
    return;

  inlining_decoratort decorated(log.get_message_handler());
  goto_function_inline(
    goto_functions, function_name, ns, log.get_message_handler());

  INVARIANT(
    decorated.get_recursive_function_warnings_count() == 0,
    "Recursive functions found during inlining");

  // restore internal invariants
  goto_functions.update();

  local_may_aliast local_may_alias(goto_function);
  natural_loops_mutablet natural_loops(goto_function.body);

  // A graph node type that stores information about a loop.
  // We create a DAG representing nesting of various loops in goto_function,
  // sort them topologically, and instrument them in the top-sorted order.
  //
  // The goal here is not avoid explicit "subset checks" on nested write sets.
  // When instrumenting in a top-sorted order,
  // the outer loop would no longer observe the inner loop's write set,
  // but only corresponding `havoc` statements,
  // which can be instrumented in the usual way to achieve a "subset check".

  struct loop_graph_nodet : public graph_nodet<empty_edget>
  {
    const typename natural_loops_mutablet::loopt &content;
    const goto_programt::targett head_target, end_target;
    exprt assigns_clause, invariant, decreases_clause;

    loop_graph_nodet(
      const typename natural_loops_mutablet::loopt &loop,
      const goto_programt::targett head,
      const goto_programt::targett end,
      const exprt &assigns,
      const exprt &inv,
      const exprt &decreases)
      : content(loop),
        head_target(head),
        end_target(end),
        assigns_clause(assigns),
        invariant(inv),
        decreases_clause(decreases)
    {
    }
  };
  grapht<loop_graph_nodet> loop_nesting_graph;

  std::list<size_t> to_check_contracts_on_children;

  for(const auto &loop_head_and_content : natural_loops.loop_map)
  {
    const auto &loop_content = loop_head_and_content.second;
    if(loop_content.empty())
      continue;

    auto loop_head = loop_head_and_content.first;
    auto loop_end = loop_head;

    // Find the last back edge to `loop_head`
    for(const auto &t : loop_content)
    {
      if(
        t->is_goto() && t->get_target() == loop_head &&
        t->location_number > loop_end->location_number)
        loop_end = t;
    }

    if(loop_end == loop_head)
    {
      log.error() << "Could not find end of the loop starting at: "
                  << loop_head->source_location() << messaget::eom;
      throw 0;
    }

    exprt assigns_clause =
      static_cast<const exprt &>(loop_end->condition().find(ID_C_spec_assigns));
    exprt invariant = static_cast<const exprt &>(
      loop_end->get_condition().find(ID_C_spec_loop_invariant));
    exprt decreases_clause = static_cast<const exprt &>(
      loop_end->get_condition().find(ID_C_spec_decreases));

    if(invariant.is_nil())
    {
      if(decreases_clause.is_not_nil() || assigns_clause.is_not_nil())
      {
        invariant = true_exprt{};
        // assigns clause is missing; we will try to automatic inference
        log.warning()
          << "The loop at " << loop_head->source_location().as_string()
          << " does not have an invariant in its contract.\n"
          << "Hence, a default invariant ('true') is being used.\n"
          << "This choice is sound, but verification may fail"
          << " if it is be too weak to prove the desired properties."
          << messaget::eom;
      }
    }
    else
    {
      invariant = conjunction(invariant.operands());
      if(decreases_clause.is_nil())
      {
        log.warning() << "The loop at "
                      << loop_head->source_location().as_string()
                      << " does not have a decreases clause in its contract.\n"
                      << "Termination of this loop will not be verified."
                      << messaget::eom;
      }
    }

    const auto idx = loop_nesting_graph.add_node(
      loop_content,
      loop_head,
      loop_end,
      assigns_clause,
      invariant,
      decreases_clause);

    if(
      assigns_clause.is_nil() && invariant.is_nil() &&
      decreases_clause.is_nil())
      continue;

    to_check_contracts_on_children.push_back(idx);

    // By definition the `loop_content` is a set of instructions computed
    // by `natural_loops` based on the CFG.
    // Since we perform assigns clause instrumentation by sequentially
    // traversing instructions from `loop_head` to `loop_end`, here check that:
    // 1. All instructions in `loop_content` are contained within the
    //    [loop_head, loop_end] iterator range
    // 2. All instructions in the [loop_head, loop_end] range are contained
    //    in the `loop_content` set, except for the exceptions explained below.

    // Check 1. (i \in loop_content) ==> loop_head <= i <= loop_end
    for(const auto &i : loop_content)
    {
      if(std::distance(loop_head, i) < 0 || std::distance(i, loop_end) < 0)
      {
        log.error() << "Computed loop at " << loop_head->source_location()
                    << "contains an instruction beyond [loop_head, loop_end]:"
                    << messaget::eom;
        goto_function.body.output_instruction(
          ns, function_name, log.error(), *i);
        throw 0;
      }
    }

    // Check 2. (loop_head <= i <= loop_end) ==> (i \in loop_content)
    //
    // We allow the following exceptions in this check:
    // - `SKIP` or `LOCATION` instructions which are no-op
    // - `ASSUME(false)` instructions which are introduced by function pointer
    //    or nested loop transformations, and have no successor instructions
    // - `SET_RETURN_VALUE` instructions followed by an uninterrupted sequence
    //    of `DEAD` instructions and a `GOTO` jump out of the loop,
    //    which model C `return` statements.
    // - `GOTO` jumps out of the loops, which model C `break` statements.
    // These instructions are allowed to be missing from `loop_content`,
    // and may be safely ignored for the purpose of our instrumentation.
    for(auto i = loop_head; i < loop_end; ++i)
    {
      if(loop_content.contains(i))
        continue;

      if(i->is_skip() || i->is_location())
        continue;

      if(i->is_goto() && !loop_content.contains(i->get_target()))
        continue;

      if(i->is_assume() && i->get_condition().is_false())
        continue;

      if(i->is_set_return_value())
      {
        do
          i++;
        while(i->is_dead());

        // because we increment `i` in the outer `for` loop
        i--;
        continue;
      }

      log.error() << "Computed loop at: " << loop_head->source_location()
                  << "is missing an instruction:" << messaget::eom;
      goto_function.body.output_instruction(ns, function_name, log.error(), *i);
      throw 0;
    }
  }

  for(size_t outer = 0; outer < loop_nesting_graph.size(); ++outer)
  {
    for(size_t inner = 0; inner < loop_nesting_graph.size(); ++inner)
    {
      if(inner == outer)
        continue;

      if(loop_nesting_graph[outer].content.contains(
           loop_nesting_graph[inner].head_target))
      {
        if(!loop_nesting_graph[outer].content.contains(
             loop_nesting_graph[inner].end_target))
        {
          log.error()
            << "Overlapping loops at:\n"
            << loop_nesting_graph[outer].head_target->source_location()
            << "\nand\n"
            << loop_nesting_graph[inner].head_target->source_location()
            << "\nLoops must be nested or sequential for contracts to be "
               "enforced."
            << messaget::eom;
        }
        loop_nesting_graph.add_edge(inner, outer);
      }
    }
  }

  // make sure all children of a contractified loop also have contracts
  while(!to_check_contracts_on_children.empty())
  {
    const auto loop_idx = to_check_contracts_on_children.front();
    to_check_contracts_on_children.pop_front();

    const auto &loop_node = loop_nesting_graph[loop_idx];
    if(
      loop_node.assigns_clause.is_nil() && loop_node.invariant.is_nil() &&
      loop_node.decreases_clause.is_nil())
    {
      log.error()
        << "Inner loop at: " << loop_node.head_target->source_location()
        << " does not have contracts, but an enclosing loop does.\n"
        << "Please provide contracts for this loop, or unwind it first."
        << messaget::eom;
      throw 0;
    }

    for(const auto child_idx : loop_nesting_graph.get_predecessors(loop_idx))
      to_check_contracts_on_children.push_back(child_idx);
  }

  // Iterate over the (natural) loops in the function, in topo-sorted order,
  // and apply any loop contracts that we find.
  for(const auto &idx : loop_nesting_graph.topsort())
  {
    const auto &loop_node = loop_nesting_graph[idx];
    if(
      loop_node.assigns_clause.is_nil() && loop_node.invariant.is_nil() &&
      loop_node.decreases_clause.is_nil())
      continue;

    check_apply_loop_contracts(
      function_name,
      goto_function,
      local_may_alias,
      loop_node.head_target,
      loop_node.end_target,
      loop_node.content,
      loop_node.assigns_clause,
      loop_node.invariant,
      loop_node.decreases_clause,
      symbol_table.lookup_ref(function_name).mode);
  }
}

symbol_tablet &code_contractst::get_symbol_table()
{
  return symbol_table;
}

goto_functionst &code_contractst::get_goto_functions()
{
  return goto_functions;
}

bool code_contractst::check_frame_conditions_function(const irep_idt &function)
{
  // Get the function object before instrumentation.
  auto function_obj = goto_functions.function_map.find(function);
  if(function_obj == goto_functions.function_map.end())
  {
    log.error() << "Could not find function '" << function
                << "' in goto-program; not enforcing contracts."
                << messaget::eom;
    return true;
  }

  const auto &goto_function = function_obj->second;
  auto &function_body = function_obj->second.body;

  // Get assigns clause for function
  const symbolt &function_symbol = ns.lookup(function);
  const auto &function_with_contract =
    to_code_with_contract_type(function_symbol.type);

  instrument_spec_assignst instrument_spec_assigns(
    function, goto_functions, symbol_table, log.get_message_handler());

  // Detect and track static local variables before inlining
  goto_programt snapshot_static_locals;
  instrument_spec_assigns.track_static_locals(snapshot_static_locals);

  // Full inlining of the function body
  // Inlining is performed so that function calls to a same function
  // occurring under different write sets get instrumented specifically
  // for each write set
  inlining_decoratort decorated(log.get_message_handler());
  goto_function_inline(goto_functions, function, ns, decorated);

  INVARIANT(
    decorated.get_recursive_function_warnings_count() == 0,
    "Recursive functions found during inlining");

  // Clean up possible fake loops that are due to `IF 0!=0 GOTO i` instructions
  simplify_gotos(function_body, ns);

  // Restore internal coherence in the programs
  goto_functions.update();

  INVARIANT(
    is_loop_free(function_body, ns, log),
    "Loops remain in function '" + id2string(function) +
      "', assigns clause checking instrumentation cannot be applied.");

  // Create a deep copy of the inlined body before any instrumentation is added
  // and compute static control flow graph information
  goto_functiont goto_function_orig;
  goto_function_orig.copy_from(goto_function);
  cfg_infot cfg_info(ns, goto_function_orig);
  optionalt<cfg_infot> cfg_info_opt{cfg_info};

  // Start instrumentation
  auto instruction_it = function_body.instructions.begin();

  // Inject local static snapshots
  insert_before_swap_and_advance(
    function_body, instruction_it, snapshot_static_locals);

  // Track targets mentionned in the specification
  for(auto &target : function_with_contract.assigns())
  {
    goto_programt payload;
    instrument_spec_assigns.track_spec_target(target, payload);
    insert_before_swap_and_advance(function_body, instruction_it, payload);
  }

  // Track formal parameters
  goto_programt snapshot_function_parameters;
  for(const auto &param : to_code_type(function_symbol.type).parameters())
  {
    goto_programt payload;
    instrument_spec_assigns.track_stack_allocated(
      ns.lookup(param.get_identifier()).symbol_expr(), payload);
    insert_before_swap_and_advance(function_body, instruction_it, payload);
  }

  // Restore internal coherence in the programs
  goto_functions.update();

  // Insert write set inclusion checks.
  instrument_spec_assigns.instrument_instructions(
    function_body,
    instruction_it,
    function_body.instructions.end(),
    skip_function_paramst::YES,
    cfg_info_opt);

  return false;
}

bool code_contractst::enforce_contract(const irep_idt &function)
{
  // Add statements to the source function
  // to ensure assigns clause is respected.
  check_frame_conditions_function(function);

  // Rename source function
  std::stringstream ss;
  ss << CPROVER_PREFIX << "contracts_original_" << function;
  const irep_idt mangled(ss.str());
  const irep_idt original(function);

  auto old_function = goto_functions.function_map.find(original);
  if(old_function == goto_functions.function_map.end())
  {
    log.error() << "Could not find function '" << function
                << "' in goto-program; not enforcing contracts."
                << messaget::eom;
    return true;
  }

  std::swap(goto_functions.function_map[mangled], old_function->second);
  goto_functions.function_map.erase(old_function);

  // Place a new symbol with the mangled name into the symbol table
  source_locationt sl;
  sl.set_file("instrumented for code contracts");
  sl.set_line("0");
  symbolt mangled_sym;
  const symbolt *original_sym = symbol_table.lookup(original);
  mangled_sym = *original_sym;
  mangled_sym.name = mangled;
  mangled_sym.base_name = mangled;
  mangled_sym.location = sl;
  const auto mangled_found = symbol_table.insert(std::move(mangled_sym));
  INVARIANT(
    mangled_found.second,
    "There should be no existing function called " + ss.str() +
      " in the symbol table because that name is a mangled name");

  // Insert wrapper function into goto_functions
  auto nexist_old_function = goto_functions.function_map.find(original);
  INVARIANT(
    nexist_old_function == goto_functions.function_map.end(),
    "There should be no function called " + id2string(function) +
      " in the function map because that function should have had its"
      " name mangled");

  auto mangled_fun = goto_functions.function_map.find(mangled);
  INVARIANT(
    mangled_fun != goto_functions.function_map.end(),
    "There should be a function called " + ss.str() +
      " in the function map because we inserted a fresh goto-program"
      " with that mangled name");

  goto_functiont &wrapper = goto_functions.function_map[original];
  wrapper.parameter_identifiers = mangled_fun->second.parameter_identifiers;
  wrapper.body.add(goto_programt::make_end_function(sl));
  add_contract_check(original, mangled, wrapper.body);

  return false;
}

void code_contractst::add_contract_check(
  const irep_idt &wrapper_function,
  const irep_idt &mangled_function,
  goto_programt &dest)
{
  PRECONDITION(!dest.instructions.empty());

  const symbolt &function_symbol = ns.lookup(mangled_function);
  const auto &code_type = to_code_with_contract_type(function_symbol.type);

  auto assigns = code_type.assigns();
  auto requires = conjunction(code_type.requires());
  auto ensures = conjunction(code_type.ensures());

  // build:
  // if(nondet)
  //   decl ret
  //   decl parameter1 ...
  //   decl history_parameter1 ... [optional]
  //   assume(requires)  [optional]
  //   ret=function(parameter1, ...)
  //   assert(ensures)
  // skip: ...

  // build skip so that if(nondet) can refer to it
  goto_programt tmp_skip;
  goto_programt::targett skip =
    tmp_skip.add(goto_programt::make_skip(ensures.source_location()));

  goto_programt check;

  // prepare function call including all declarations
  code_function_callt call(function_symbol.symbol_expr());

  // Create a replace_symbolt object, for replacing expressions in the callee
  // with expressions from the call site (e.g. the return value).
  // This object tracks replacements that are common to ENSURES and REQUIRES.
  replace_symbolt common_replace;

  // decl ret
  optionalt<code_returnt> return_stmt;
  if(code_type.return_type() != empty_typet())
  {
    symbol_exprt r = new_tmp_symbol(
                       code_type.return_type(),
                       skip->source_location(),
                       function_symbol.mode,
                       symbol_table)
                       .symbol_expr();
    check.add(goto_programt::make_decl(r, skip->source_location()));

    call.lhs() = r;
    return_stmt = code_returnt(r);

    symbol_exprt ret_val(CPROVER_PREFIX "return_value", call.lhs().type());
    common_replace.insert(ret_val, r);
  }

  // decl parameter1 ...
  goto_functionst::function_mapt::iterator f_it =
    goto_functions.function_map.find(mangled_function);
  PRECONDITION(f_it != goto_functions.function_map.end());

  const goto_functionst::goto_functiont &gf = f_it->second;
  for(const auto &parameter : gf.parameter_identifiers)
  {
    PRECONDITION(!parameter.empty());
    const symbolt &parameter_symbol = ns.lookup(parameter);
    symbol_exprt p = new_tmp_symbol(
                       parameter_symbol.type,
                       skip->source_location(),
                       parameter_symbol.mode,
                       symbol_table)
                       .symbol_expr();
    check.add(goto_programt::make_decl(p, skip->source_location()));
    check.add(goto_programt::make_assignment(
      p, parameter_symbol.symbol_expr(), skip->source_location()));

    call.arguments().push_back(p);

    common_replace.insert(parameter_symbol.symbol_expr(), p);
  }

  is_fresh_enforcet visitor(*this, log, wrapper_function);
  visitor.create_declarations();

  // Generate: assume(requires)
  if(!requires.is_false())
  {
    // extend common_replace with quantified variables in REQUIRES,
    // and then do the replacement
    replace_symbolt replace(common_replace);
    code_contractst::add_quantified_variable(
      requires, replace, function_symbol.mode);
    replace(requires);

    goto_programt assumption;
    converter.goto_convert(
      code_assumet(requires), assumption, function_symbol.mode);
    visitor.update_requires(assumption);
    check.destructive_append(assumption);
  }

  // Prepare the history variables handling
  std::pair<goto_programt, goto_programt> ensures_pair;

  // Generate: copies for history variables
  if(!ensures.is_true())
  {
    // extend common_replace with quantified variables in ENSURES,
    // and then do the replacement
    replace_symbolt replace(common_replace);
    code_contractst::add_quantified_variable(
      ensures, replace, function_symbol.mode);
    replace(ensures);

    // get all the relevant instructions related to history variables
    auto assertion = code_assertt(ensures);
    assertion.add_source_location() = ensures.source_location();
    ensures_pair = create_ensures_instruction(
      assertion, ensures.source_location(), function_symbol.mode);
    ensures_pair.first.instructions.back()
      .source_location_nonconst()
      .set_comment("Check ensures clause");
    ensures_pair.first.instructions.back()
      .source_location_nonconst()
      .set_property_class(ID_postcondition);

    // add all the history variable initializations
    visitor.update_ensures(ensures_pair.first);
    check.destructive_append(ensures_pair.second);
  }

  // ret=mangled_function(parameter1, ...)
  check.add(goto_programt::make_function_call(call, skip->source_location()));

  // Generate: assert(ensures)
  if(ensures.is_not_nil())
  {
    check.destructive_append(ensures_pair.first);
  }

  if(code_type.return_type() != empty_typet())
  {
    check.add(goto_programt::make_set_return_value(
      return_stmt.value().return_value(), skip->source_location()));
  }

  // prepend the new code to dest
  check.destructive_append(tmp_skip);
  dest.destructive_insert(dest.instructions.begin(), check);
}

bool code_contractst::replace_calls(const std::set<std::string> &to_replace)
{
  if(to_replace.empty())
    return false;

  bool fail = false;

  for(auto &goto_function : goto_functions.function_map)
  {
    Forall_goto_program_instructions(ins, goto_function.second.body)
    {
      if(ins->is_function_call())
      {
        if(ins->call_function().id() != ID_symbol)
          continue;

        const irep_idt &called_function =
          to_symbol_expr(ins->call_function()).get_identifier();
        auto found = std::find(
          to_replace.begin(), to_replace.end(), id2string(called_function));
        if(found == to_replace.end())
          continue;

        fail |= apply_function_contract(
          goto_function.first,
          ins->source_location(),
          goto_function.second.body,
          ins);
      }
    }
  }

  if(fail)
    return true;

  for(auto &goto_function : goto_functions.function_map)
    remove_skip(goto_function.second.body);

  goto_functions.update();

  return false;
}

void code_contractst::apply_loop_contracts()
{
  for(auto &goto_function : goto_functions.function_map)
    apply_loop_contract(goto_function.first, goto_function.second);
}

bool code_contractst::enforce_contracts(const std::set<std::string> &to_enforce)
{
  if(to_enforce.empty())
    return false;

  bool fail = false;

  for(const auto &function : to_enforce)
  {
    auto goto_function = goto_functions.function_map.find(function);
    if(goto_function == goto_functions.function_map.end())
    {
      fail = true;
      log.error() << "Could not find function '" << function
                  << "' in goto-program; not enforcing contracts."
                  << messaget::eom;
      continue;
    }

    if(!fail)
      fail = enforce_contract(function);
  }
  return fail;
}
