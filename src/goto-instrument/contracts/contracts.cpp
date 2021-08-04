/*******************************************************************\

Module: Verify and use annotated invariants and pre/post-conditions

Author: Michael Tautschnig

Date: February 2016

\*******************************************************************/

/// \file
/// Verify and use annotated invariants and pre/post-conditions

#include "contracts.h"

#include "assigns.h"
#include "memory_predicates.h"

#include <algorithm>
#include <map>

#include <analyses/local_may_alias.h>

#include <ansi-c/c_expr.h>

#include <goto-programs/remove_skip.h>

#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>
#include <util/message.h>
#include <util/pointer_offset_size.h>
#include <util/replace_symbol.h>

// Create a lexicographic less-than relation between two tuples of variables.
// This is used in the implementation of multidimensional decreases clauses.
static exprt create_lexicographic_less_than(
  const std::vector<symbol_exprt> &lhs,
  const std::vector<symbol_exprt> &rhs)
{
  PRECONDITION(lhs.size() == rhs.size());

  if(lhs.empty())
  {
    return false_exprt();
  }

  // Store conjunctions of equalities.
  // For example, suppose that the two input vectors are <s1, s2, s3> and <l1,
  // l2, l3>.
  // Then this vector stores <s1 == l1, s1 == l1 && s2 == l2,
  // s1 == l1 && s2 == l2 && s3 == l3>.
  // In fact, the last element is unnecessary, so we do not create it.
  exprt::operandst equality_conjunctions(lhs.size());
  equality_conjunctions[0] = binary_relation_exprt(lhs[0], ID_equal, rhs[0]);
  for(size_t i = 1; i < equality_conjunctions.size() - 1; i++)
  {
    binary_relation_exprt component_i_equality{lhs[i], ID_equal, rhs[i]};
    equality_conjunctions[i] =
      and_exprt(equality_conjunctions[i - 1], component_i_equality);
  }

  // Store inequalities between the i-th components of the input vectors
  // (i.e. lhs and rhs).
  // For example, suppose that the two input vectors are <s1, s2, s3> and <l1,
  // l2, l3>.
  // Then this vector stores <s1 < l1, s1 == l1 && s2 < l2, s1 == l1 &&
  // s2 == l2 && s3 < l3>.
  exprt::operandst lexicographic_individual_comparisons(lhs.size());
  lexicographic_individual_comparisons[0] =
    binary_relation_exprt(lhs[0], ID_lt, rhs[0]);
  for(size_t i = 1; i < lexicographic_individual_comparisons.size(); i++)
  {
    binary_relation_exprt component_i_less_than{lhs[i], ID_lt, rhs[i]};
    lexicographic_individual_comparisons[i] =
      and_exprt(equality_conjunctions[i - 1], component_i_less_than);
  }
  return disjunction(lexicographic_individual_comparisons);
}

static void insert_before_swap_and_advance(
  goto_programt &program,
  goto_programt::targett &target,
  goto_programt &payload)
{
  const auto offset = payload.instructions.size();
  program.insert_before_swap(target, payload);
  std::advance(target, offset);
}

void code_contractst::check_apply_loop_contracts(
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

  // see whether we have an invariant and a decreases clause
  auto invariant = static_cast<const exprt &>(
    loop_end->get_condition().find(ID_C_spec_loop_invariant));
  auto decreases_clause = static_cast<const exprt &>(
    loop_end->get_condition().find(ID_C_spec_decreases));

  if(invariant.is_nil())
  {
    if(decreases_clause.is_nil())
      return;
    else
    {
      invariant = true_exprt();
      log.warning()
        << "The loop at " << loop_head->source_location.as_string()
        << " does not have a loop invariant, but has a decreases clause. "
        << "Hence, a default loop invariant ('true') is being used."
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
  //   H: assert(invariant);
  //   havoc;
  //   assume(invariant);
  //   if(guard) goto E:
  //   old_decreases_value = decreases_clause(current_environment);
  //   loop;
  //   new_decreases_value = decreases_clause(current_environment);
  //   assert(invariant);
  //   assert(new_decreases_value < old_decreases_value);
  //   assume(false);
  //   E: ...

  // find out what can get changed in the loop
  modifiest modifies;
  get_modifies(local_may_alias, loop, modifies);

  // build the havocking code
  goto_programt havoc_code;

  // process quantified variables correctly (introduce a fresh temporary)
  // and return a copy of the invariant
  const auto &invariant_expr = [&]() {
    auto invariant_copy = invariant;
    replace_symbolt replace;
    code_contractst::add_quantified_variable(invariant_copy, replace, mode);
    replace(invariant_copy);
    return invariant_copy;
  };

  // Generate: assert(invariant) just before the loop
  // We use a block scope to create a temporary assertion,
  // and immediately convert it to goto instructions.
  {
    code_assertt assertion{invariant_expr()};
    assertion.add_source_location() = loop_head->source_location;
    converter.goto_convert(assertion, havoc_code, mode);
    havoc_code.instructions.back().source_location.set_comment(
      "Check loop invariant before entry");
  }

  // havoc variables being written to
  build_havoc_code(loop_head, modifies, havoc_code);

  // Generate: assume(invariant) just after havocing
  // We use a block scope to create a temporary assumption,
  // and immediately convert it to goto instructions.
  {
    code_assumet assumption{invariant_expr()};
    assumption.add_source_location() = loop_head->source_location;
    converter.goto_convert(assumption, havoc_code, mode);
  }

  // Create fresh temporary variables that store the multidimensional
  // decreases clause's value before and after the loop
  for(const auto &clause : decreases_clause.operands())
  {
    const auto old_decreases_var =
      new_tmp_symbol(clause.type(), loop_head->source_location, mode)
        .symbol_expr();
    havoc_code.add(
      goto_programt::make_decl(old_decreases_var, loop_head->source_location));
    old_decreases_vars.push_back(old_decreases_var);

    const auto new_decreases_var =
      new_tmp_symbol(clause.type(), loop_head->source_location, mode)
        .symbol_expr();
    havoc_code.add(
      goto_programt::make_decl(new_decreases_var, loop_head->source_location));
    new_decreases_vars.push_back(new_decreases_var);
  }

  // non-deterministically skip the loop if it is a do-while loop
  if(!loop_head->is_goto())
  {
    havoc_code.add(goto_programt::make_goto(
      loop_end,
      side_effect_expr_nondett(bool_typet(), loop_head->source_location)));
  }

  // Now havoc at the loop head.
  // Use insert_before_swap to preserve jumps to loop head.
  insert_before_swap_and_advance(goto_function.body, loop_head, havoc_code);

  // Generate: assignments to store the multidimensional decreases clause's
  // value before the loop
  if(!decreases_clause.is_nil())
  {
    for(size_t i = 0; i < old_decreases_vars.size(); i++)
    {
      code_assignt old_decreases_assignment{old_decreases_vars[i],
                                            decreases_clause_exprs[i]};
      old_decreases_assignment.add_source_location() =
        loop_head->source_location;
      converter.goto_convert(old_decreases_assignment, havoc_code, mode);
    }

    goto_function.body.destructive_insert(std::next(loop_head), havoc_code);
  }

  // Generate: assert(invariant) just after the loop exits
  // We use a block scope to create a temporary assertion,
  // and immediately convert it to goto instructions.
  {
    code_assertt assertion{invariant_expr()};
    assertion.add_source_location() = loop_end->source_location;
    converter.goto_convert(assertion, havoc_code, mode);
    havoc_code.instructions.back().source_location.set_comment(
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
        loop_head->source_location;
      converter.goto_convert(new_decreases_assignment, havoc_code, mode);
    }

    // Generate: assertion that the multidimensional decreases clause's value
    // after the loop is smaller than the value before the loop.
    // Here, we use the lexicographic order.
    code_assertt monotonic_decreasing_assertion{
      create_lexicographic_less_than(new_decreases_vars, old_decreases_vars)};
    monotonic_decreasing_assertion.add_source_location() =
      loop_head->source_location;
    converter.goto_convert(monotonic_decreasing_assertion, havoc_code, mode);
    havoc_code.instructions.back().source_location.set_comment(
      "Check decreases clause on loop iteration");

    // Discard the temporary variables that store decreases clause's value
    for(size_t i = 0; i < old_decreases_vars.size(); i++)
    {
      havoc_code.add(goto_programt::make_dead(
        old_decreases_vars[i], loop_head->source_location));
      havoc_code.add(goto_programt::make_dead(
        new_decreases_vars[i], loop_head->source_location));
    }
  }

  insert_before_swap_and_advance(goto_function.body, loop_end, havoc_code);

  // change the back edge into assume(false) or assume(guard)
  loop_end->targets.clear();
  loop_end->type = ASSUME;
  if(loop_head->is_goto())
    loop_end->set_condition(false_exprt());
  else
    loop_end->set_condition(boolean_negate(loop_end->get_condition()));
}

bool code_contractst::has_contract(const irep_idt fun_name)
{
  const symbolt &function_symbol = ns.lookup(fun_name);
  const auto &type = to_code_with_contract_type(function_symbol.type);
  return type.has_contract();
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
      symbolt new_symbol = get_fresh_aux_symbol(
        quantified_symbol.type(),
        id2string(quantified_symbol.get_identifier()),
        "tmp",
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

void code_contractst::replace_old_parameter(
  exprt &expr,
  std::map<exprt, exprt> &parameter2history,
  source_locationt location,
  const irep_idt &mode,
  goto_programt &history)
{
  for(auto &op : expr.operands())
  {
    replace_old_parameter(op, parameter2history, location, mode, history);
  }

  if(expr.id() == ID_old)
  {
    DATA_INVARIANT(
      expr.operands().size() == 1, CPROVER_PREFIX "old must have one operand");

    const auto &parameter = to_old_expr(expr).expression();

    // TODO: generalize below
    if(parameter.id() == ID_dereference)
    {
      const auto &dereference_expr = to_dereference_expr(parameter);

      auto it = parameter2history.find(dereference_expr);

      if(it == parameter2history.end())
      {
        // 1. Create a temporary symbol expression that represents the
        // history variable
        symbol_exprt tmp_symbol =
          new_tmp_symbol(dereference_expr.type(), location, mode).symbol_expr();

        // 2. Associate the above temporary variable to it's corresponding
        // expression
        parameter2history[dereference_expr] = tmp_symbol;

        // 3. Add the required instructions to the instructions list
        // 3.1 Declare the newly created temporary variable
        history.add(goto_programt::make_decl(tmp_symbol, location));

        // 3.2 Add an assignment such that the value pointed to by the new
        // temporary variable is equal to the value of the corresponding
        // parameter
        history.add(goto_programt::make_assignment(
          tmp_symbol, dereference_expr, location));
      }

      expr = parameter2history[dereference_expr];
    }
    else
    {
      log.error() << CPROVER_PREFIX "old does not currently support "
                  << parameter.id() << " expressions." << messaget::eom;
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
  replace_old_parameter(expression, parameter2history, location, mode, history);

  // Create instructions corresponding to the ensures clause
  goto_programt ensures_program;
  converter.goto_convert(expression, ensures_program, mode);

  // return a pair containing:
  // 1. instructions corresponding to the ensures clause
  // 2. instructions related to initializing the history variables
  return std::make_pair(std::move(ensures_program), std::move(history));
}

bool code_contractst::apply_function_contract(
  goto_programt &goto_program,
  goto_programt::targett target)
{
  const code_function_callt &call = target->get_function_call();

  // Return if the function is not named in the call; currently we don't handle
  // function pointers.
  PRECONDITION(call.function().id() == ID_symbol);

  // Retrieve the function type, which is needed to extract the contract
  // components.
  const irep_idt &function = to_symbol_expr(call.function()).get_identifier();
  const symbolt &function_symbol = ns.lookup(function);
  const auto &type = to_code_with_contract_type(function_symbol.type);

  // Isolate each component of the contract.
  auto assigns = type.assigns();
  auto requires = conjunction(type.requires());
  auto ensures = conjunction(type.ensures());

  // Create a replace_symbolt object, for replacing expressions in the callee
  // with expressions from the call site (e.g. the return value).
  // This object tracks replacements that are common to ENSURES and REQUIRES.
  replace_symbolt common_replace;
  if(type.return_type() != empty_typet())
  {
    // Check whether the function's return value is not disregarded.
    if(call.lhs().is_not_nil())
    {
      // If so, have it replaced appropriately.
      // For example, if foo() ensures that its return value is > 5, then
      // rewrite calls to foo as follows:
      // x = foo() -> assume(__CPROVER_return_value > 5) -> assume(x > 5)
      symbol_exprt ret_val(CPROVER_PREFIX "return_value", call.lhs().type());
      common_replace.insert(ret_val, call.lhs());
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
          id2string(function),
          "ignored_return_value",
          call.source_location(),
          symbol_table.lookup_ref(function).mode,
          ns,
          symbol_table);
        symbol_exprt ret_val(CPROVER_PREFIX "return_value", type.return_type());
        common_replace.insert(ret_val, fresh.symbol_expr());
      }
    }
  }

  // Replace formal parameters
  auto a_it = call.arguments().begin();
  for(auto p_it = type.parameters().begin();
      p_it != type.parameters().end() && a_it != call.arguments().end();
      ++p_it, ++a_it)
  {
    if(!p_it->get_identifier().empty())
    {
      symbol_exprt p(p_it->get_identifier(), p_it->type());
      common_replace.insert(p, *a_it);
    }
  }

  // ASSIGNS clause should not refer to any quantified variables,
  // and only refer to the common symbols to be replaced.
  common_replace(assigns);

  const auto &mode = symbol_table.lookup_ref(function).mode;

  is_fresh_replacet is_fresh(*this, log, function);
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
      symbol_table.lookup_ref(function).mode);
    assertion.instructions.back().source_location = requires.source_location();
    assertion.instructions.back().source_location.set_comment(
      "Check requires clause");
    assertion.instructions.back().source_location.set_property_class(
      ID_precondition);
    is_fresh.update_requires(assertion);
    insert_before_swap_and_advance(goto_program, target, assertion);
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
      symbol_table.lookup_ref(function).mode);

    // add all the history variable initialization instructions
    // to the goto program
    insert_before_swap_and_advance(goto_program, target, ensures_pair.second);
  }

  // Create a series of non-deterministic assignments to havoc the variables
  // in the assigns clause.
  if(assigns.is_not_nil())
  {
    assigns_clauset assigns_cause(assigns, *this, function, log);
    goto_programt assigns_havoc = assigns_cause.havoc_code();

    // Insert the non-deterministic assignment immediately before the call site.
    insert_before_swap_and_advance(goto_program, target, assigns_havoc);
  }

  // To remove the function call, insert statements related to the assumption.
  // Then, replace the function call with a SKIP statement.
  if(!ensures.is_false())
  {
    is_fresh.update_ensures(ensures_pair.first);
    insert_before_swap_and_advance(goto_program, target, ensures_pair.first);
  }
  *target = goto_programt::make_skip();

  // Add this function to the set of replaced functions.
  summarized.insert(function);
  return false;
}

void code_contractst::apply_loop_contract(
  const irep_idt &function,
  goto_functionst::goto_functiont &goto_function)
{
  local_may_aliast local_may_alias(goto_function);
  natural_loops_mutablet natural_loops(goto_function.body);

  // Iterate over the (natural) loops in the function,
  // and apply any invariant annotations that we find.
  for(const auto &loop : natural_loops.loop_map)
  {
    check_apply_loop_contracts(
      goto_function,
      local_may_alias,
      loop.first,
      loop.second,
      symbol_table.lookup_ref(function).mode);
  }
}

const symbolt &code_contractst::new_tmp_symbol(
  const typet &type,
  const source_locationt &source_location,
  const irep_idt &mode)
{
  return get_fresh_aux_symbol(
    type,
    id2string(source_location.get_function()) + "::tmp_cc",
    "tmp_cc",
    source_location,
    mode,
    symbol_table);
}

symbol_tablet &code_contractst::get_symbol_table()
{
  return symbol_table;
}

goto_functionst &code_contractst::get_goto_functions()
{
  return goto_functions;
}

exprt code_contractst::create_alias_expression(
  const exprt &lhs,
  std::vector<exprt> &aliasable_references)
{
  exprt::operandst operands;
  operands.reserve(aliasable_references.size());
  for(auto aliasable : aliasable_references)
  {
    operands.push_back(equal_exprt(lhs, typecast_exprt(aliasable, lhs.type())));
  }
  return disjunction(operands);
}

void code_contractst::instrument_assign_statement(
  goto_programt::instructionst::iterator &instruction_iterator,
  goto_programt &program,
  exprt &assigns,
  std::set<irep_idt> &freely_assignable_symbols,
  assigns_clauset &assigns_clause)
{
  INVARIANT(
    instruction_iterator->is_assign(),
    "The first instruction of instrument_assign_statement should always be"
    " an assignment");

  const exprt &lhs = instruction_iterator->assign_lhs();

  goto_programt alias_assertion;
  alias_assertion.add(goto_programt::make_assertion(
    assigns_clause.alias_expression(lhs),
    instruction_iterator->source_location));
  alias_assertion.instructions.back().source_location.set_comment(
    "Check that " + from_expr(ns, lhs.id(), lhs) + " is assignable");
  insert_before_swap_and_advance(
    program, instruction_iterator, alias_assertion);
}

void code_contractst::instrument_call_statement(
  goto_programt::instructionst::iterator &instruction_iterator,
  goto_programt &program,
  exprt &assigns,
  std::set<irep_idt> &freely_assignable_symbols,
  assigns_clauset &assigns_clause)
{
  INVARIANT(
    instruction_iterator->is_function_call(),
    "The first argument of instrument_call_statement should always be "
    "a function call");

  code_function_callt call = instruction_iterator->get_function_call();
  irep_idt called_name;
  if(call.function().id() == ID_dereference)
  {
    called_name = to_symbol_expr(to_dereference_expr(call.function()).pointer())
                    .get_identifier();
  }
  else
  {
    called_name = to_symbol_expr(call.function()).get_identifier();
  }

  if(called_name == "malloc")
  {
    // malloc statments return a void pointer, which is then cast and assigned
    // to a result variable. We iterate one line forward to grab the result of
    // the malloc once it is cast.
    instruction_iterator++;
    if(instruction_iterator->is_assign())
    {
      const exprt &rhs = instruction_iterator->assign_rhs();
      INVARIANT(
        rhs.id() == ID_typecast,
        "malloc is called but the result is not cast. Excluding result from "
        "the assignable memory frame.");
      typet cast_type = rhs.type();

      // Make freshly allocated memory assignable, if we can determine its type.
      assigns_clause_targett *new_target =
        assigns_clause.add_target(dereference_exprt(rhs));
      goto_programt &pointer_capture = new_target->get_init_block();
      insert_before_swap_and_advance(
        program, instruction_iterator, pointer_capture);
    }
    return; // assume malloc edits no pre-existing memory objects.
  }

  if(
    call.lhs().is_not_nil() && call.lhs().id() == ID_symbol &&
    freely_assignable_symbols.find(
      to_symbol_expr(call.lhs()).get_identifier()) ==
      freely_assignable_symbols.end())
  {
    exprt alias_expr = assigns_clause.alias_expression(call.lhs());

    goto_programt alias_assertion;
    alias_assertion.add(goto_programt::make_assertion(
      alias_expr, instruction_iterator->source_location));
    alias_assertion.instructions.back().source_location.set_comment(
      "Check that " + from_expr(ns, alias_expr.id(), alias_expr) +
      " is assignable");
    program.insert_before_swap(instruction_iterator, alias_assertion);
    ++instruction_iterator;
  }

  const symbolt &called_symbol = ns.lookup(called_name);
  // Called symbol might be a function pointer.
  const typet &called_symbol_type = (called_symbol.type.id() == ID_pointer)
                                      ? called_symbol.type.subtype()
                                      : called_symbol.type;
  exprt called_assigns =
    to_code_with_contract_type(called_symbol_type).assigns();
  const code_typet &called_type = to_code_type(called_symbol_type);

  if(called_assigns.is_not_nil())
  {
    replace_symbolt replace_formal_params;
    auto a_it = call.arguments().begin();
    for(auto p_it = called_type.parameters().begin();
        p_it != called_type.parameters().end() &&
        a_it != call.arguments().end();
        ++p_it, ++a_it)
    {
      if(!p_it->get_identifier().empty())
      {
        symbol_exprt p(p_it->get_identifier(), p_it->type());
        replace_formal_params.insert(p, *a_it);
      }
    }
    replace_formal_params(called_assigns);

    // check compatibility of assigns clause with the called function
    assigns_clauset called_assigns_clause(
      called_assigns, *this, called_name, log);
    exprt compatible =
      assigns_clause.compatible_expression(called_assigns_clause);
    goto_programt alias_assertion;
    alias_assertion.add(goto_programt::make_assertion(
      compatible, instruction_iterator->source_location));
    alias_assertion.instructions.back().source_location.set_comment(
      "Check compatibility of assigns clause with the called function");
    program.insert_before_swap(instruction_iterator, alias_assertion);
    ++instruction_iterator;
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
      code_function_callt call = instruction.get_function_call();
      irep_idt called_name;
      if(call.function().id() == ID_dereference)
      {
        called_name =
          to_symbol_expr(to_dereference_expr(call.function()).pointer())
            .get_identifier();
      }
      else
      {
        called_name = to_symbol_expr(call.function()).get_identifier();
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
  auto old_function = goto_functions.function_map.find(function);
  if(old_function == goto_functions.function_map.end())
  {
    log.error() << "Could not find function '" << function
                << "' in goto-program; not enforcing contracts."
                << messaget::eom;
    return true;
  }
  goto_programt &program = old_function->second.body;
  if(program.instructions.empty()) // empty function body
  {
    return false;
  }

  if(check_for_looped_mallocs(program))
  {
    return true;
  }

  // Insert aliasing assertions
  check_frame_conditions(program, ns.lookup(function));

  return false;
}

void code_contractst::check_frame_conditions(
  goto_programt &program,
  const symbolt &target)
{
  const auto &type = to_code_with_contract_type(target.type);
  exprt assigns_expr = type.assigns();

  assigns_clauset assigns(assigns_expr, *this, target.name, log);

  // Create a list of variables that are okay to assign.
  std::set<irep_idt> freely_assignable_symbols;
  // Add all parameters that are not pointers to the freely assignable set
  for(code_typet::parametert param : type.parameters())
  {
    if(param.type().id() != ID_pointer)
    {
      freely_assignable_symbols.insert(param.get_identifier());
    }
  }

  // Create temporary variables to hold the assigns
  // clause targets before they can be modified.
  goto_programt standin_decls = assigns.init_block();
  // Create dead statements for temporary variables
  goto_programt mark_dead = assigns.dead_stmts();

  // Skip lines with temporary variable declarations
  auto instruction_it = program.instructions.begin();
  insert_before_swap_and_advance(program, instruction_it, standin_decls);

  for(; instruction_it != program.instructions.end(); ++instruction_it)
  {
    if(instruction_it->is_decl())
    {
      freely_assignable_symbols.insert(
        instruction_it->get_decl().symbol().get_identifier());

      assigns_clause_targett *new_target =
        assigns.add_target(instruction_it->get_decl().symbol());
      goto_programt &pointer_capture = new_target->get_init_block();

      for(auto in : pointer_capture.instructions)
      {
        program.insert_after(instruction_it, in);
        ++instruction_it;
      }
    }
    else if(instruction_it->is_assign())
    {
      instrument_assign_statement(
        instruction_it,
        program,
        assigns_expr,
        freely_assignable_symbols,
        assigns);
    }
    else if(instruction_it->is_function_call())
    {
      instrument_call_statement(
        instruction_it,
        program,
        assigns_expr,
        freely_assignable_symbols,
        assigns);
    }
  }

  // Walk the iterator back to the last statement
  while(!instruction_it->is_end_function())
  {
    --instruction_it;
  }

  // Make sure the temporary symbols are marked dead
  program.insert_before_swap(instruction_it, mark_dead);
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

  exprt assigns = code_type.assigns();
  exprt requires = conjunction(code_type.requires());
  exprt ensures = conjunction(code_type.ensures());

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
  code_returnt return_stmt;
  if(code_type.return_type() != empty_typet())
  {
    symbol_exprt r = new_tmp_symbol(
                       code_type.return_type(),
                       skip->source_location,
                       function_symbol.mode)
                       .symbol_expr();
    check.add(goto_programt::make_decl(r, skip->source_location));

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
                       skip->source_location,
                       parameter_symbol.mode)
                       .symbol_expr();
    check.add(goto_programt::make_decl(p, skip->source_location));
    check.add(goto_programt::make_assignment(
      p, parameter_symbol.symbol_expr(), skip->source_location));

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
    ensures_pair.first.instructions.back().source_location.set_comment(
      "Check ensures clause");
    ensures_pair.first.instructions.back().source_location.set_property_class(
      ID_postcondition);

    // add all the history variable initializations
    visitor.update_ensures(ensures_pair.first);
    check.destructive_append(ensures_pair.second);
  }

  // ret=mangled_function(parameter1, ...)
  check.add(goto_programt::make_function_call(call, skip->source_location));

  // Generate: assert(ensures)
  if(ensures.is_not_nil())
  {
    check.destructive_append(ensures_pair.first);
  }

  if(code_type.return_type() != empty_typet())
  {
    check.add(goto_programt::make_return(return_stmt, skip->source_location));
  }

  // prepend the new code to dest
  check.destructive_append(tmp_skip);
  dest.destructive_insert(dest.instructions.begin(), check);
}

bool code_contractst::replace_calls(const std::set<std::string> &functions)
{
  bool fail = false;
  for(const auto &function : functions)
  {
    if(!has_contract(function))
    {
      log.error() << "Function '" << function
                  << "' does not have a contract; "
                     "not replacing calls with contract."
                  << messaget::eom;
      fail = true;
    }
  }
  if(fail)
    return true;

  for(auto &goto_function : goto_functions.function_map)
  {
    Forall_goto_program_instructions(ins, goto_function.second.body)
    {
      if(ins->is_function_call())
      {
        const code_function_callt &call = ins->get_function_call();

        if(call.function().id() != ID_symbol)
          continue;

        const irep_idt &called_function =
          to_symbol_expr(call.function()).get_identifier();
        auto found = std::find(
          functions.begin(), functions.end(), id2string(called_function));
        if(found == functions.end())
          continue;

        fail |= apply_function_contract(goto_function.second.body, ins);
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

bool code_contractst::replace_calls()
{
  std::set<std::string> functions;
  for(auto &goto_function : goto_functions.function_map)
  {
    if(has_contract(goto_function.first))
      functions.insert(id2string(goto_function.first));
  }
  return replace_calls(functions);
}

bool code_contractst::enforce_contracts()
{
  std::set<std::string> functions;
  for(auto &goto_function : goto_functions.function_map)
  {
    if(has_contract(goto_function.first))
      functions.insert(id2string(goto_function.first));
  }
  return enforce_contracts(functions);
}

bool code_contractst::enforce_contracts(const std::set<std::string> &functions)
{
  bool fail = false;
  for(const auto &function : functions)
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

    if(!has_contract(function))
    {
      fail = true;
      log.error() << "Could not find any contracts within function '"
                  << function << "'; nothing to enforce." << messaget::eom;
      continue;
    }

    if(!fail)
      fail = enforce_contract(function);
  }
  return fail;
}
