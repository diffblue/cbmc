/*******************************************************************\

Module: Utility functions for code contracts.

Author: Saswat Padhi, saspadhi@amazon.com

Date: September 2021

\*******************************************************************/

#include "utils.h"

#include <util/c_types.h>
#include <util/fresh_symbol.h>
#include <util/graph.h>
#include <util/mathematical_expr.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>
#include <util/symbol.h>

#include <goto-programs/cfg.h>

#include <ansi-c/c_expr.h>
#include <langapi/language_util.h>

static void append_safe_havoc_code_for_expr(
  const source_locationt location,
  const namespacet &ns,
  const exprt &expr,
  goto_programt &dest,
  const std::function<void()> &havoc_code_impl)
{
  goto_programt skip_program;
  const auto skip_target = skip_program.add(goto_programt::make_skip(location));

  // skip havocing only if all pointer derefs in the expression are valid
  // (to avoid spurious pointer deref errors)
  dest.add(goto_programt::make_goto(
    skip_target, not_exprt{all_dereferences_are_valid(expr, ns)}, location));

  havoc_code_impl();

  // add the final skip target
  dest.destructive_append(skip_program);
}

void havoc_assigns_targetst::append_havoc_slice_code(
  const source_locationt location,
  const exprt &ptr,
  const exprt &size,
  goto_programt &dest)
{
  append_safe_havoc_code_for_expr(
    location,
    ns,
    ptr,
    dest,
    // clang-format off
    [&]() {
      symbol_exprt function{CPROVER_PREFIX "havoc_slice", empty_typet()};
      function.add_source_location() = location;
      // havoc slice is lowered to array operations during goto conversion
      // so we use goto_convertt directly as provided by clearnert
      cleaner.do_havoc_slice(function, {ptr, size}, dest, mode);
    });
  // clang-format on
}

void havoc_assigns_targetst::append_havoc_pointer_code(
  const source_locationt location,
  const exprt &ptr_to_ptr,
  goto_programt &dest)
{
  append_safe_havoc_code_for_expr(location, ns, ptr_to_ptr, dest, [&]() {
    auto ptr = dereference_exprt(ptr_to_ptr);
    dest.add(goto_programt::make_assignment(
      ptr, side_effect_expr_nondett(ptr.type(), location), location));
  });
}

void havoc_if_validt::append_object_havoc_code_for_expr(
  const source_locationt location,
  const exprt &expr,
  goto_programt &dest) const
{
  append_safe_havoc_code_for_expr(location, ns, expr, dest, [&]() {
    havoc_utilst::append_object_havoc_code_for_expr(location, expr, dest);
  });
}

void havoc_if_validt::append_scalar_havoc_code_for_expr(
  const source_locationt location,
  const exprt &expr,
  goto_programt &dest) const
{
  append_safe_havoc_code_for_expr(location, ns, expr, dest, [&]() {
    havoc_utilst::append_scalar_havoc_code_for_expr(location, expr, dest);
  });
}

void havoc_assigns_targetst::append_havoc_code_for_expr(
  const source_locationt location,
  const exprt &expr,
  goto_programt &dest)
{
  if(expr.id() == ID_pointer_object)
  {
    // pointer_object is still used internally to support malloc/free
    append_object_havoc_code_for_expr(
      location, to_pointer_object_expr(expr).pointer(), dest);
    return;
  }
  else if(can_cast_expr<side_effect_expr_function_callt>(expr))
  {
    const auto &funcall = to_side_effect_expr_function_call(expr);
    // type-checking ensures the function expression is necessarily a symbol
    const auto &ident = to_symbol_expr(funcall.function()).get_identifier();
    if(ident == CPROVER_PREFIX "object_whole")
    {
      append_object_havoc_code_for_expr(
        location, funcall.arguments().at(0), dest);
    }
    else if(ident == CPROVER_PREFIX "object_from")
    {
      const auto ptr = typecast_exprt::conditional_cast(
        funcall.arguments().at(0), pointer_type(char_type()));

      exprt obj_size = object_size(ptr);
      minus_exprt size{
        obj_size,
        typecast_exprt::conditional_cast(pointer_offset(ptr), obj_size.type())};

      append_havoc_slice_code(expr.source_location(), ptr, size, dest);
    }
    else if(ident == CPROVER_PREFIX "object_upto")
    {
      const auto ptr = typecast_exprt::conditional_cast(
        funcall.arguments().at(0), pointer_type(char_type()));
      const auto size = typecast_exprt::conditional_cast(
        funcall.arguments().at(1), size_type());
      append_havoc_slice_code(expr.source_location(), ptr, size, dest);
    }
    else if(ident == CPROVER_PREFIX "assignable")
    {
      const auto &ptr = funcall.arguments().at(0);
      const auto &size = funcall.arguments().at(1);
      if(funcall.arguments().at(2).is_true())
      {
        append_havoc_pointer_code(expr.source_location(), ptr, dest);
      }
      else
      {
        append_havoc_slice_code(expr.source_location(), ptr, size, dest);
      }
    }
    else
    {
      UNREACHABLE;
    }
  }
  else
  {
    // we have an lvalue expression, make nondet assignment
    havoc_utilst::append_havoc_code_for_expr(location, expr, dest);
  }
}

exprt all_dereferences_are_valid(const exprt &expr, const namespacet &ns)
{
  exprt::operandst validity_checks;

  if(auto deref = expr_try_dynamic_cast<dereference_exprt>(expr))
  {
    const auto size_of_expr_opt = size_of_expr(expr.type(), ns);
    CHECK_RETURN(size_of_expr_opt.has_value());

    symbol_exprt deallocated =
      ns.lookup(CPROVER_PREFIX "deallocated").symbol_expr();
    symbol_exprt dead = ns.lookup(CPROVER_PREFIX "dead_object").symbol_expr();
    validity_checks.push_back(prophecy_r_ok_exprt{
      deref->pointer(), *size_of_expr_opt, deallocated, dead});
  }

  for(const auto &op : expr.operands())
    validity_checks.push_back(all_dereferences_are_valid(op, ns));

  return conjunction(validity_checks);
}

exprt generate_lexicographic_less_than_check(
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

void insert_before_swap_and_advance(
  goto_programt &destination,
  goto_programt::targett &target,
  goto_programt &payload)
{
  const auto offset = payload.instructions.size();
  destination.insert_before_swap(target, payload);
  std::advance(target, offset);
}

void insert_before_and_update_jumps(
  goto_programt &destination,
  goto_programt::targett &target,
  const goto_programt::instructiont &i)
{
  const auto new_target = destination.insert_before(target, i);
  for(auto it : target->incoming_edges)
  {
    if(it->is_goto())
      it->set_target(new_target);
  }
}

void simplify_gotos(goto_programt &goto_program, namespacet &ns)
{
  for(auto &instruction : goto_program.instructions)
  {
    if(
      instruction.is_goto() &&
      simplify_expr(instruction.condition(), ns).is_false())
      instruction.turn_into_skip();
  }
}

bool is_loop_free(
  const goto_programt &goto_program,
  namespacet &ns,
  messaget &log)
{
  // create cfg from instruction list
  cfg_baset<empty_cfg_nodet> cfg;
  cfg(goto_program);

  // check that all nodes are there
  INVARIANT(
    goto_program.instructions.size() == cfg.size(),
    "Instruction list vs CFG size mismatch.");

  // compute SCCs
  using idxt = graph_nodet<empty_cfg_nodet>::node_indext;
  std::vector<idxt> node_to_scc(cfg.size(), -1);
  auto nof_sccs = cfg.SCCs(node_to_scc);

  // compute size of each SCC
  std::vector<int> scc_size(nof_sccs, 0);
  for(auto scc : node_to_scc)
  {
    INVARIANT(
      0 <= scc && scc < nof_sccs, "Could not determine SCC for instruction");
    scc_size[scc]++;
  }

  // check they are all of size 1
  for(size_t scc_id = 0; scc_id < nof_sccs; scc_id++)
  {
    auto size = scc_size[scc_id];
    if(size > 1)
    {
      log.conditional_output(
        log.error(),
        [&cfg, &node_to_scc, &scc_id, &size](messaget::mstreamt &mstream) {
          mstream << "Found CFG SCC with size " << size << messaget::eom;
          for(const auto &node_id : node_to_scc)
          {
            if(node_to_scc[node_id] == scc_id)
            {
              const auto &pc = cfg[node_id].PC;
              pc->output(mstream);
              mstream << messaget::eom;
            }
          }
        });
      return false;
    }
  }
  return true;
}

/// Prefix for comments added to track assigns clause replacement.
static const char ASSIGNS_CLAUSE_REPLACEMENT_TRACKING[] =
  " (assigned by the contract of ";

irep_idt make_assigns_clause_replacement_tracking_comment(
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

void widen_assigns(assignst &assigns, const namespacet &ns)
{
  assignst result;

  havoc_utils_is_constantt is_constant(assigns, ns);

  for(const auto &e : assigns)
  {
    if(e.id() == ID_index || e.id() == ID_dereference)
    {
      address_of_exprt address_of_expr(e);

      // index or offset is non-constant.
      if(!is_constant(address_of_expr))
      {
        result.emplace(pointer_object(address_of_expr));
      }
      else
        result.emplace(e);
    }
    else
      result.emplace(e);
  }
  assigns = result;
}

void add_quantified_variable(
  symbol_table_baset &symbol_table,
  exprt &expression,
  const irep_idt &mode)
{
  if(expression.id() == ID_not || expression.id() == ID_typecast)
  {
    // For unary connectives, recursively check for
    // nested quantified formulae in the term
    auto &unary_expression = to_unary_expr(expression);
    add_quantified_variable(symbol_table, unary_expression.op(), mode);
  }
  if(expression.id() == ID_notequal || expression.id() == ID_implies)
  {
    // For binary connectives, recursively check for
    // nested quantified formulae in the left and right terms
    auto &binary_expression = to_binary_expr(expression);
    add_quantified_variable(symbol_table, binary_expression.lhs(), mode);
    add_quantified_variable(symbol_table, binary_expression.rhs(), mode);
  }
  if(expression.id() == ID_if)
  {
    // For ternary connectives, recursively check for
    // nested quantified formulae in all three terms
    auto &if_expression = to_if_expr(expression);
    add_quantified_variable(symbol_table, if_expression.cond(), mode);
    add_quantified_variable(symbol_table, if_expression.true_case(), mode);
    add_quantified_variable(symbol_table, if_expression.false_case(), mode);
  }
  if(expression.id() == ID_and || expression.id() == ID_or)
  {
    // For multi-ary connectives, recursively check for
    // nested quantified formulae in all terms
    auto &multi_ary_expression = to_multi_ary_expr(expression);
    for(auto &operand : multi_ary_expression.operands())
    {
      add_quantified_variable(symbol_table, operand, mode);
    }
  }
  else if(expression.id() == ID_exists || expression.id() == ID_forall)
  {
    // When a quantifier expression is found, create a fresh symbol for each
    // quantified variable and rewrite the expression to use those fresh
    // symbols.
    auto &quantifier_expression = to_quantifier_expr(expression);
    std::vector<symbol_exprt> fresh_variables;
    fresh_variables.reserve(quantifier_expression.variables().size());
    for(const auto &quantified_variable : quantifier_expression.variables())
    {
      // 1. create fresh symbol
      symbolt new_symbol = get_fresh_aux_symbol(
        quantified_variable.type(),
        id2string(quantified_variable.source_location().get_function()),
        "tmp_cc",
        quantified_variable.source_location(),
        mode,
        symbol_table);

      // 2. add created fresh symbol to expression map
      fresh_variables.push_back(new_symbol.symbol_expr());
    }

    // use fresh symbols
    exprt where = quantifier_expression.instantiate(fresh_variables);

    // recursively check for nested quantified formulae
    add_quantified_variable(symbol_table, where, mode);

    // replace previous variables and body
    quantifier_expression.variables() = fresh_variables;
    quantifier_expression.where() = std::move(where);
  }
}

static void replace_history_parameter_rec(
  symbol_table_baset &symbol_table,
  exprt &expr,
  std::unordered_map<exprt, symbol_exprt, irep_hash> &parameter2history,
  const source_locationt &location,
  const irep_idt &mode,
  goto_programt &history,
  const irep_idt &history_id)
{
  for(auto &op : expr.operands())
  {
    replace_history_parameter_rec(
      symbol_table, op, parameter2history, location, mode, history, history_id);
  }

  if(expr.id() != ID_old && expr.id() != ID_loop_entry)
    return;

  const auto &parameter = to_history_expr(expr, history_id).expression();
  const auto &id = parameter.id();
  DATA_INVARIANT_WITH_DIAGNOSTICS(
    id == ID_dereference || id == ID_member || id == ID_symbol ||
      id == ID_ptrmember || id == ID_constant || id == ID_typecast ||
      id == ID_index,
    "Tracking history of " + id2string(id) +
      " expressions is not supported yet.",
    parameter.pretty());

  // speculatively insert a dummy, which will be replaced below if the insert
  // actually happened
  auto entry =
    parameter2history.insert({parameter, symbol_exprt::typeless(ID_nil)});

  if(entry.second)
  {
    // 1. Create a temporary symbol expression that represents the
    // history variable
    entry.first->second = get_fresh_aux_symbol(
                            parameter.type(),
                            id2string(location.get_function()),
                            "tmp_cc",
                            location,
                            mode,
                            symbol_table)
                            .symbol_expr();

    // 2. Add the required instructions to the instructions list
    // 2.1. Declare the newly created temporary variable
    history.add(goto_programt::make_decl(entry.first->second, location));

    // 2.2. Skip storing the history if the expression is invalid
    auto goto_instruction = history.add(goto_programt::make_incomplete_goto(
      not_exprt{
        all_dereferences_are_valid(parameter, namespacet(symbol_table))},
      location));

    // 2.3. Add an assignment such that the value pointed to by the new
    // temporary variable is equal to the value of the corresponding
    // parameter
    history.add(
      goto_programt::make_assignment(entry.first->second, parameter, location));

    // 2.4. Complete conditional jump for invalid-parameter case
    auto label_instruction = history.add(goto_programt::make_skip(location));
    goto_instruction->complete_goto(label_instruction);
  }

  expr = entry.first->second;
}

replace_history_parametert replace_history_old(
  symbol_table_baset &symbol_table,
  const exprt &expr,
  const source_locationt &location,
  const irep_idt &mode)
{
  replace_history_parametert result;
  result.expression_after_replacement = expr;
  replace_history_parameter_rec(
    symbol_table,
    result.expression_after_replacement,
    result.parameter_to_history,
    location,
    mode,
    result.history_construction,
    ID_old);
  return result;
}

replace_history_parametert replace_history_loop_entry(
  symbol_table_baset &symbol_table,
  const exprt &expr,
  const source_locationt &location,
  const irep_idt &mode)
{
  replace_history_parametert result;
  result.expression_after_replacement = expr;
  replace_history_parameter_rec(
    symbol_table,
    result.expression_after_replacement,
    result.parameter_to_history,
    location,
    mode,
    result.history_construction,
    ID_loop_entry);
  return result;
}

void generate_history_variables_initialization(
  symbol_table_baset &symbol_table,
  exprt &clause,
  const irep_idt &mode,
  goto_programt &program)
{
  // Find and replace "old" expression in the "expression" variable
  auto result =
    replace_history_old(symbol_table, clause, clause.source_location(), mode);
  clause.swap(result.expression_after_replacement);
  // Add all the history variable initialization instructions
  program.destructive_append(result.history_construction);
}

bool is_transformed_loop_head(const goto_programt::const_targett &target)
{
  // The head of a transformed loop is
  // ASSIGN entered_loop = false
  return is_assignment_to_instrumented_variable(target, ENTERED_LOOP) &&
         target->assign_rhs() == false_exprt();
}

bool is_transformed_loop_end(const goto_programt::const_targett &target)
{
  // The end of a transformed loop is
  // ASSIGN entered_loop = true
  return is_assignment_to_instrumented_variable(target, ENTERED_LOOP) &&
         target->assign_rhs() == true_exprt();
}

bool is_assignment_to_instrumented_variable(
  const goto_programt::const_targett &target,
  std::string var_name)
{
  INVARIANT(
    var_name == IN_BASE_CASE || var_name == ENTERED_LOOP ||
      var_name == IN_LOOP_HAVOC_BLOCK,
    "var_name is not of instrumented variables.");

  if(!target->is_assign())
    return false;

  if(can_cast_expr<symbol_exprt>(target->assign_lhs()))
  {
    const auto &lhs = to_symbol_expr(target->assign_lhs());
    return id2string(lhs.get_identifier()).find("::" + var_name) !=
           std::string::npos;
  }

  return false;
}

unsigned get_suffix_unsigned(const std::string &str, const std::string &prefix)
{
  // first_index is the end of the `prefix`.
  auto first_index = str.find(prefix);
  INVARIANT(
    first_index != std::string::npos, "Prefix not found in the given string");
  first_index += prefix.length();

  // last_index is the index of not-digit.
  auto last_index = str.find_first_not_of("0123456789", first_index);
  std::string result = str.substr(first_index, last_index - first_index);
  return std::stol(result);
}
