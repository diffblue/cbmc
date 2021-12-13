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
  const loopt &loop,
  const irep_idt &mode)
{
  PRECONDITION(!loop.empty());

  // find the last back edge
  goto_programt::targett loop_end = loop_head;
  for(const auto &t : loop)
    if(
      t->is_goto() && t->get_target() == loop_head &&
      t->location_number > loop_end->location_number)
      loop_end = t;

  // check for assigns, invariant, and decreases clauses
  auto assigns_clause = static_cast<const exprt &>(
    loop_end->get_condition().find(ID_C_spec_assigns));
  auto invariant = static_cast<const exprt &>(
    loop_end->get_condition().find(ID_C_spec_loop_invariant));
  auto decreases_clause = static_cast<const exprt &>(
    loop_end->get_condition().find(ID_C_spec_decreases));

  assigns_clauset loop_assigns(
    assigns_clause.operands(), log, ns, function_name, symbol_table);

  loop_assigns.add_static_locals_to_write_set(goto_functions, function_name);

  if(invariant.is_nil())
  {
    if(decreases_clause.is_nil() && assigns_clause.is_nil())
      return;
    else
    {
      invariant = true_exprt();
      log.warning()
        << "The loop at " << loop_head->source_location().as_string()
        << " does not have an invariant, but has other clauses"
        << " specified in its contract.\n"
        << "Hence, a default invariant ('true') is being used to prove those."
        << messaget::eom;
    }
  }
  else
  {
    // form the conjunction
    invariant = conjunction(invariant.operands());
  }

  // Vector representing a (possibly multidimensional) decreases clause
  const auto &decreases_clause_exprs = decreases_clause.operands();

  // Temporary variables for storing the multidimensional decreases clause
  // at the start of and end of a loop body
  std::vector<symbol_exprt> old_decreases_vars;
  std::vector<symbol_exprt> new_decreases_vars;

  // change
  //   H: loop;
  //   E: ...
  // to
  //   initialize loop_entry variables;
  //   H: assert(invariant);
  //   snapshot(write_set);
  //   havoc;
  //   assume(invariant);
  //   if(guard) goto E:
  //   old_decreases_value = decreases_clause_expr;
  //   loop with optional write_set inclusion checks;
  //   new_decreases_value = decreases_clause_expr;
  //   assert(invariant);
  //   assert(new_decreases_value < old_decreases_value);
  //   assume(false);
  //   E: ...

  // an intermediate goto_program to store generated instructions
  goto_programt generated_code;

  // process quantified variables correctly (introduce a fresh temporary)
  // and return a copy of the invariant
  const auto &invariant_expr = [&]() {
    auto invariant_copy = invariant;
    replace_symbolt replace;
    code_contractst::add_quantified_variable(invariant_copy, replace, mode);
    replace(invariant_copy);
    return invariant_copy;
  };

  // Process "loop_entry" history variables
  // Find and replace "loop_entry" expression in the "invariant" expression.
  std::map<exprt, exprt> parameter2history;
  replace_history_parameter(
    invariant,
    parameter2history,
    loop_head->source_location(),
    mode,
    generated_code,
    ID_loop_entry);

  // Generate: assert(invariant) just before the loop
  // We use a block scope to create a temporary assertion,
  // and immediately convert it to goto instructions.
  {
    code_assertt assertion{invariant_expr()};
    assertion.add_source_location() = loop_head->source_location();
    converter.goto_convert(assertion, generated_code, mode);
    generated_code.instructions.back().source_location_nonconst().set_comment(
      "Check loop invariant before entry");
  }

  // Add 'loop_entry' history variables and base case assertion.
  // These variables are local and thus
  // need not be checked against the enclosing scope's write set.
  insert_before_swap_and_advance(
    goto_function.body,
    loop_head,
    add_pragma_disable_assigns_check(generated_code));

  assignst to_havoc;

  if(assigns_clause.is_nil())
  {
    // No assigns clause was specified for this loop.
    // Infer memory locations assigned by the loop from the loop instructions
    // and the inferred aliasing relation.
    try
    {
      get_assigns(local_may_alias, loop, to_havoc);
      log.debug() << "No loop assigns clause provided. Inferred targets {";
      // Add inferred targets to the loop assigns clause.
      bool ran_once = false;
      for(const auto &target : to_havoc)
      {
        if(ran_once)
          log.debug() << ", ";
        ran_once = true;
        log.debug() << format(target);
        loop_assigns.add_to_write_set(target);
      }
      log.debug()
        << "}. Please specify an assigns clause if verification fails."
        << messaget::eom;
    }
    catch(const analysis_exceptiont &exc)
    {
      log.error() << "Failed to infer variables being modified by the loop at "
                  << loop_head->source_location()
                  << ".\nPlease specify an assigns clause.\nReason:"
                  << messaget::eom;
      throw exc;
    }
  }
  else
  {
    // An assigns clause was specified for this loop.
    // Add the targets to the set of expressions to havoc.
    // TODO: Should we add the automatically detected local static variables
    // too ? (they are present in loop_assigns but not in assigns_clause, and
    // they are not necessarily touched by the loop).
    to_havoc.insert(
      assigns_clause.operands().cbegin(), assigns_clause.operands().cend());
  }

  // Create snapshots of write set CARs.
  // This must be done before havocing the write set.
  for(const auto &car : loop_assigns.get_write_set())
  {
    auto snapshot_instructions = car.generate_snapshot_instructions();
    insert_before_swap_and_advance(
      goto_function.body, loop_head, snapshot_instructions);
  };

  // Perform write set instrumentation on the entire loop.
  check_frame_conditions(
    function_name,
    goto_function.body,
    loop_head,
    loop_end,
    loop_assigns,
    // do not skip checks on function parameter assignments
    false);

  havoc_assigns_targetst havoc_gen(to_havoc, ns);
  havoc_gen.append_full_havoc_code(
    loop_head->source_location(), generated_code);

  // Add the havocing code, but only check against the enclosing scope's
  // write set if it was manually specified.
  if(assigns_clause.is_nil())
    insert_before_swap_and_advance(
      goto_function.body,
      loop_head,
      add_pragma_disable_assigns_check(generated_code));
  else
    insert_before_swap_and_advance(
      goto_function.body, loop_head, generated_code);

  // Generate: assume(invariant) just after havocing
  // We use a block scope to create a temporary assumption,
  // and immediately convert it to goto instructions.
  {
    code_assumet assumption{invariant_expr()};
    assumption.add_source_location() = loop_head->source_location();
    converter.goto_convert(assumption, generated_code, mode);
  }

  // Create fresh temporary variables that store the multidimensional
  // decreases clause's value before and after the loop
  for(const auto &clause : decreases_clause.operands())
  {
    const auto old_decreases_var =
      new_tmp_symbol(
        clause.type(), loop_head->source_location(), mode, symbol_table)
        .symbol_expr();
    generated_code.add(goto_programt::make_decl(
      old_decreases_var, loop_head->source_location()));
    old_decreases_vars.push_back(old_decreases_var);

    const auto new_decreases_var =
      new_tmp_symbol(
        clause.type(), loop_head->source_location(), mode, symbol_table)
        .symbol_expr();
    generated_code.add(goto_programt::make_decl(
      new_decreases_var, loop_head->source_location()));
    new_decreases_vars.push_back(new_decreases_var);
  }

  // TODO: Fix loop contract handling for do/while loops.
  if(loop_end->is_goto() && !loop_end->get_condition().is_true())
  {
    log.error() << "Loop contracts are unsupported on do/while loops: "
                << loop_head->source_location() << messaget::eom;
    throw 0;

    // non-deterministically skip the loop if it is a do-while loop.
    generated_code.add(goto_programt::make_goto(
      loop_end,
      side_effect_expr_nondett(bool_typet(), loop_head->source_location())));
  }

  // Assume invariant & decl the variant temporaries (just before loop guard).
  // Use insert_before_swap to preserve jumps to loop head.
  insert_before_swap_and_advance(
    goto_function.body,
    loop_head,
    add_pragma_disable_assigns_check(generated_code));

  // Forward the loop_head iterator until the start of the body.
  // This is necessary because complex C loop_head conditions could be
  // converted to multiple GOTO instructions (e.g. temporaries are introduced).
  // If the loop_head location shifts to a different function,
  // assume that it's an inlined function and keep skipping.
  // FIXME: This simple approach wouldn't work when
  // the loop guard in the source file is split across multiple lines.
  const auto head_loc = loop_head->source_location();
  while(loop_head->source_location() == head_loc ||
        loop_head->source_location().get_function() != head_loc.get_function())
    loop_head++;

  // At this point, we are just past the loop head,
  // so at the beginning of the loop body.
  auto loop_body = loop_head;
  loop_head--;

  // Generate: assignments to store the multidimensional decreases clause's
  // value just before the loop body (but just after the loop guard)
  if(!decreases_clause.is_nil())
  {
    for(size_t i = 0; i < old_decreases_vars.size(); i++)
    {
      code_assignt old_decreases_assignment{old_decreases_vars[i],
                                            decreases_clause_exprs[i]};
      old_decreases_assignment.add_source_location() =
        loop_head->source_location();
      converter.goto_convert(old_decreases_assignment, generated_code, mode);
    }

    goto_function.body.destructive_insert(
      loop_body, add_pragma_disable_assigns_check(generated_code));
  }

  // Generate: assert(invariant) just after the loop exits
  // We use a block scope to create a temporary assertion,
  // and immediately convert it to goto instructions.
  {
    code_assertt assertion{invariant_expr()};
    assertion.add_source_location() = loop_end->source_location();
    converter.goto_convert(assertion, generated_code, mode);
    generated_code.instructions.back().source_location_nonconst().set_comment(
      "Check that loop invariant is preserved");
  }

  // Generate: assignments to store the multidimensional decreases clause's
  // value after one iteration of the loop
  if(!decreases_clause.is_nil())
  {
    for(size_t i = 0; i < new_decreases_vars.size(); i++)
    {
      code_assignt new_decreases_assignment{new_decreases_vars[i],
                                            decreases_clause_exprs[i]};
      new_decreases_assignment.add_source_location() =
        loop_head->source_location();
      converter.goto_convert(new_decreases_assignment, generated_code, mode);
    }

    // Generate: assertion that the multidimensional decreases clause's value
    // after the loop is smaller than the value before the loop.
    // Here, we use the lexicographic order.
    code_assertt monotonic_decreasing_assertion{
      generate_lexicographic_less_than_check(
        new_decreases_vars, old_decreases_vars)};
    monotonic_decreasing_assertion.add_source_location() =
      loop_head->source_location();
    converter.goto_convert(
      monotonic_decreasing_assertion, generated_code, mode);
    generated_code.instructions.back().source_location_nonconst().set_comment(
      "Check decreases clause on loop iteration");

    // Discard the temporary variables that store decreases clause's value
    for(size_t i = 0; i < old_decreases_vars.size(); i++)
    {
      generated_code.add(goto_programt::make_dead(
        old_decreases_vars[i], loop_head->source_location()));
      generated_code.add(goto_programt::make_dead(
        new_decreases_vars[i], loop_head->source_location()));
    }
  }

  insert_before_swap_and_advance(
    goto_function.body,
    loop_end,
    add_pragma_disable_assigns_check(generated_code));

  // change the back edge into assume(false) or assume(guard)
  loop_end->turn_into_assume();
  loop_end->set_condition(boolean_negate(loop_end->get_condition()));
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

    if(
      parameter.id() == ID_dereference || parameter.id() == ID_member ||
      parameter.id() == ID_symbol || parameter.id() == ID_ptrmember)
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

  // Create a sequence of non-deterministic assignments...
  goto_programt havoc_instructions;

  // ...for assigns clause targets
  if(!assigns_clause.empty())
  {
    assigns_clauset assigns_clause(
      targets.operands(), log, ns, target_function, symbol_table);

    // Havoc all targets in the write set
    assignst assigns;
    assigns.insert(targets.operands().cbegin(), targets.operands().cend());

    havoc_assigns_targetst havoc_gen(assigns, ns);
    havoc_gen.append_full_havoc_code(location, havoc_instructions);
  }

  // ...for the return value
  if(call_ret_opt.has_value())
  {
    auto &call_ret = call_ret_opt.value();
    auto &loc = call_ret.source_location();
    auto &type = call_ret.type();
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
    typedef const goto_programt::targett &targett;
    typedef const typename natural_loops_mutablet::loopt &loopt;

    targett target;
    loopt loop;

    loop_graph_nodet(targett t, loopt l) : target(t), loop(l)
    {
    }
  };
  grapht<loop_graph_nodet> loop_nesting_graph;

  for(const auto &loop : natural_loops.loop_map)
    loop_nesting_graph.add_node(loop.first, loop.second);

  for(size_t outer = 0; outer < loop_nesting_graph.size(); ++outer)
  {
    for(size_t inner = 0; inner < loop_nesting_graph.size(); ++inner)
    {
      if(inner == outer)
        continue;

      if(loop_nesting_graph[outer].loop.contains(
           loop_nesting_graph[inner].target))
        loop_nesting_graph.add_edge(outer, inner);
    }
  }

  // Iterate over the (natural) loops in the function, in topo-sorted order,
  // and apply any loop contracts that we find.
  for(const auto &idx : loop_nesting_graph.topsort())
  {
    const auto &loop_node = loop_nesting_graph[idx];
    check_apply_loop_contracts(
      function_name,
      goto_function,
      local_may_alias,
      loop_node.target,
      loop_node.loop,
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

void code_contractst::instrument_assign_statement(
  goto_programt::instructionst::iterator &instruction_it,
  goto_programt &program,
  assigns_clauset &assigns_clause)
{
  INVARIANT(
    instruction_it->is_assign(),
    "The first instruction of instrument_assign_statement should always be"
    " an assignment");
  add_inclusion_check(
    program, assigns_clause, instruction_it, instruction_it->assign_lhs());
}

void code_contractst::instrument_call_statement(
  goto_programt::instructionst::iterator &instruction_it,
  const irep_idt &function,
  goto_programt &body,
  assigns_clauset &assigns)
{
  INVARIANT(
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
      const auto &object = function_call.lhs();
      // move past the call and then insert the CAR
      instruction_it++;
      const auto car = assigns.add_to_write_set(pointer_object(object));
      auto snapshot_instructions = car->generate_snapshot_instructions();
      insert_before_swap_and_advance(
        body, instruction_it, snapshot_instructions);
      // since CAR was inserted *after* the malloc call,
      // move the instruction pointer backward,
      // because the caller increments it in a `for` loop
      instruction_it--;
    }
  }
  else if(callee_name == "free")
  {
    source_locationt location_no_checks = instruction_it->source_location();
    disable_pointer_checks(location_no_checks);
    const auto free_car = add_inclusion_check(
      body,
      assigns,
      instruction_it,
      pointer_object(instruction_it->call_arguments().front()));

    // skip all invalidation business if we're freeing invalid memory
    goto_programt alias_checking_instructions, skip_program;
    alias_checking_instructions.add(goto_programt::make_goto(
      skip_program.add(goto_programt::make_skip(location_no_checks)),
      not_exprt{free_car.validity_condition_var},
      location_no_checks));

    // Since the argument to free may be an "alias" (but not identical)
    // to existing CARs' source_expr, structural equality wouldn't work.
    // Moreover, multiple CARs in the writeset might be aliased to the
    // same underlying object.
    // So, we first find the corresponding CAR using `same_object` checks.
    std::unordered_set<exprt, irep_hash> write_set_validity_addrs;
    for(const auto &w_car : assigns.get_write_set())
    {
      const auto object_validity_var_addr =
        new_tmp_symbol(
          pointer_type(bool_typet{}),
          location_no_checks,
          symbol_table.lookup_ref(function).mode,
          symbol_table,
          "__car_valid")
          .symbol_expr();
      write_set_validity_addrs.insert(object_validity_var_addr);

      alias_checking_instructions.add(
        goto_programt::make_decl(object_validity_var_addr, location_no_checks));
      // if the CAR was defined on the same_object as the one being `free`d,
      // record its validity variable's address, otherwise record NULL
      alias_checking_instructions.add(goto_programt::make_assignment(
        object_validity_var_addr,
        if_exprt{
          and_exprt{
            w_car.validity_condition_var,
            same_object(
              free_car.lower_bound_address_var, w_car.lower_bound_address_var)},
          address_of_exprt{w_car.validity_condition_var},
          null_pointer_exprt{to_pointer_type(object_validity_var_addr.type())}},
        location_no_checks));
    }

    alias_checking_instructions.destructive_append(skip_program);
    insert_before_swap_and_advance(
      body,
      instruction_it,
      add_pragma_disable_assigns_check(alias_checking_instructions));

    // move past the call and then insert the invalidation instructions
    instruction_it++;

    // skip all invalidation business if we're freeing invalid memory
    goto_programt invalidation_instructions;
    skip_program.clear();
    invalidation_instructions.add(goto_programt::make_goto(
      skip_program.add(goto_programt::make_skip(location_no_checks)),
      not_exprt{free_car.validity_condition_var},
      location_no_checks));

    // invalidate all recorded CAR validity variables
    for(const auto &w_car_validity_addr : write_set_validity_addrs)
    {
      goto_programt w_car_skip_program;
      invalidation_instructions.add(goto_programt::make_goto(
        w_car_skip_program.add(goto_programt::make_skip(location_no_checks)),
        null_pointer(w_car_validity_addr),
        location_no_checks));
      invalidation_instructions.add(goto_programt::make_assignment(
        dereference_exprt{w_car_validity_addr},
        false_exprt{},
        location_no_checks));
      invalidation_instructions.destructive_append(w_car_skip_program);
    }

    invalidation_instructions.destructive_append(skip_program);
    insert_before_swap_and_advance(
      body,
      instruction_it,
      add_pragma_disable_assigns_check(invalidation_instructions));

    instruction_it--;
  }
}

bool code_contractst::check_for_looped_mallocs(const goto_programt &program)
{
  // Collect all GOTOs and mallocs
  std::vector<goto_programt::instructiont> back_gotos;
  std::vector<goto_programt::instructiont> malloc_calls;

  int index = 0;
  for(goto_programt::instructiont instruction : program.instructions)
  {
    if(instruction.is_backwards_goto())
    {
      back_gotos.push_back(instruction);
    }
    if(instruction.is_function_call())
    {
      irep_idt called_name;
      if(instruction.call_function().id() == ID_dereference)
      {
        called_name =
          to_symbol_expr(
            to_dereference_expr(instruction.call_function()).pointer())
            .get_identifier();
      }
      else
      {
        called_name =
          to_symbol_expr(instruction.call_function()).get_identifier();
      }

      if(called_name == "malloc")
      {
        malloc_calls.push_back(instruction);
      }
    }
    index++;
  }
  // Make sure there are no gotos that go back such that a malloc
  // is between the goto and its destination (possible loop).
  for(auto goto_entry : back_gotos)
  {
    for(const auto &target : goto_entry.targets)
    {
      for(auto malloc_entry : malloc_calls)
      {
        if(
          malloc_entry.location_number >= target->location_number &&
          malloc_entry.location_number < goto_entry.location_number)
        {
          log.error() << "Call to malloc at location "
                      << malloc_entry.location_number << " falls between goto "
                      << "source location " << goto_entry.location_number
                      << " and it's destination at location "
                      << target->location_number << ". "
                      << "Unable to complete instrumentation, as this malloc "
                      << "may be in a loop." << messaget::eom;
          throw 0;
        }
      }
    }
  }
  return false;
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

  if(check_for_looped_mallocs(function_obj->second.body))
  {
    return true;
  }

  // Get assigns clause for function
  const symbolt &target = ns.lookup(function);
  assigns_clauset assigns(
    to_code_with_contract_type(target.type).assigns(),
    log,
    ns,
    function,
    symbol_table);

  // detect and add static local variables
  assigns.add_static_locals_to_write_set(goto_functions, function);

  // Add formal parameters to write set
  for(const auto &param : to_code_type(target.type).parameters())
    assigns.add_to_write_set(ns.lookup(param.get_identifier()).symbol_expr());

  auto instruction_it = function_obj->second.body.instructions.begin();
  for(const auto &car : assigns.get_write_set())
  {
    auto snapshot_instructions = car.generate_snapshot_instructions();
    insert_before_swap_and_advance(
      function_obj->second.body, instruction_it, snapshot_instructions);
  };

  // Full inlining of the function body
  // Inlining is performed so that function calls to a same function
  // occurring under different write sets get instrumented specifically
  // for each write set
  inlining_decoratort decorated(log.get_message_handler());
  goto_function_inline(goto_functions, function, ns, decorated);

  INVARIANT(
    decorated.get_recursive_function_warnings_count() == 0,
    "Recursive functions found during inlining");

  // restore internal invariants
  goto_functions.update();

  // Insert write set inclusion checks.
  check_frame_conditions(
    function_obj->first,
    function_obj->second.body,
    instruction_it,
    function_obj->second.body.instructions.end(),
    assigns,
    // skip checks on function parameter assignments
    true);

  return false;
}

void code_contractst::check_frame_conditions(
  const irep_idt &function,
  goto_programt &body,
  goto_programt::targett instruction_it,
  const goto_programt::targett &instruction_end,
  assigns_clauset &assigns,
  bool skip_parameter_assigns)
{
  for(; instruction_it != instruction_end; ++instruction_it)
  {
    const auto &pragmas = instruction_it->source_location().get_pragmas();
    if(pragmas.find(CONTRACT_PRAGMA_DISABLE_ASSIGNS_CHECK) != pragmas.end())
      continue;

    if(skip_parameter_assigns && is_parameter_assign(instruction_it, ns))
      continue;

    if(is_auxiliary_decl_dead_or_assign(instruction_it, ns))
      continue;

    // Do not instrument this instruction again in the future,
    // since we are going to instrument it now below.
    add_pragma_disable_assigns_check(*instruction_it);

    if(instruction_it->is_decl())
    {
      // grab the declared symbol
      const auto &decl_symbol = instruction_it->decl_symbol();
      // move past the call and then insert the CAR
      instruction_it++;
      const auto car = assigns.add_to_write_set(decl_symbol);
      auto snapshot_instructions = car->generate_snapshot_instructions();
      insert_before_swap_and_advance(
        body, instruction_it, snapshot_instructions);
      // since CAR was inserted *after* the DECL instruction,
      // move the instruction pointer backward,
      // because the `for` loop takes care of the increment
      instruction_it--;
    }
    else if(instruction_it->is_assign())
    {
      instrument_assign_statement(instruction_it, body, assigns);
    }
    else if(instruction_it->is_function_call())
    {
      instrument_call_statement(instruction_it, function, body, assigns);
    }
    else if(instruction_it->is_dead())
    {
      const auto &symbol = instruction_it->dead_symbol();
      source_locationt location_no_checks = instruction_it->source_location();
      disable_pointer_checks(location_no_checks);

      // CAR equality and hash are defined on source_expr alone,
      // therefore this temporary CAR should be "found"
      const auto &symbol_car = assigns.get_write_set().find(
        assigns_clauset::conditional_address_ranget{assigns, symbol});
      if(symbol_car != assigns.get_write_set().end())
      {
        auto invalidation_assignment = goto_programt::make_assignment(
          symbol_car->validity_condition_var,
          false_exprt{},
          instruction_it->source_location());
        // note that the CAR must be invalidated _after_ the DEAD instruction
        body.insert_after(
          instruction_it,
          add_pragma_disable_assigns_check(invalidation_assignment));
      }
      else
      {
        // For loops, the loop_head appears after the DECL of counters,
        // and any other temporaries introduced during "initialization".
        // However, they go `DEAD` (possible conditionally) inside the loop,
        // in presence of return statements.
        // Notice that for them those variables be writable,
        // they must appear as assigns targets anyway,
        // but their DECL statements are outside of the loop.
        log.warning() << "Found a `DEAD` variable " << symbol.get_identifier()
                      << " without corresponding `DECL`, at: "
                      << instruction_it->source_location() << messaget::eom;
      }
    }
    else if(
      instruction_it->is_other() &&
      instruction_it->get_other().get_statement() == ID_havoc_object)
    {
      const auto havoc_argument =
        pointer_object(instruction_it->get_other().operands().front());
      add_inclusion_check(body, assigns, instruction_it, havoc_argument);
    }
  }
}

const assigns_clauset::conditional_address_ranget
code_contractst::add_inclusion_check(
  goto_programt &program,
  const assigns_clauset &assigns,
  goto_programt::instructionst::iterator &instruction_it,
  const exprt &expr)
{
  const assigns_clauset::conditional_address_ranget car{assigns, expr};
  auto snapshot_instructions = car.generate_snapshot_instructions();
  insert_before_swap_and_advance(
    program, instruction_it, snapshot_instructions);

  goto_programt assertion;
  source_locationt location_no_checks =
    instruction_it->source_location_nonconst();
  disable_pointer_checks(location_no_checks);
  location_no_checks.set_comment(
    "Check that " + from_expr(ns, expr.id(), expr) + " is assignable");
  assertion.add(goto_programt::make_assertion(
    assigns.generate_inclusion_check(car), location_no_checks));
  insert_before_swap_and_advance(program, instruction_it, assertion);

  return car;
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
