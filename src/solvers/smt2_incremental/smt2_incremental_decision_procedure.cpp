// Author: Diffblue Ltd.

#include "smt2_incremental_decision_procedure.h"

#include <solvers/smt2_incremental/convert_expr_to_smt.h>
#include <solvers/smt2_incremental/smt_commands.h>
#include <solvers/smt2_incremental/smt_core_theory.h>
#include <solvers/smt2_incremental/smt_responses.h>
#include <solvers/smt2_incremental/smt_solver_process.h>
#include <solvers/smt2_incremental/smt_terms.h>
#include <util/expr.h>
#include <util/namespace.h>
#include <util/nodiscard.h>
#include <util/range.h>
#include <util/std_expr.h>
#include <util/string_utils.h>
#include <util/symbol.h>

#include <stack>

/// Issues a command to the solving process which is expected to optionally
/// return a success status followed by the actual response of interest.
static smt_responset get_response_to_command(
  smt_base_solver_processt &solver_process,
  const smt_commandt &command)
{
  solver_process.send(command);
  auto response = solver_process.receive_response();
  if(response.cast<smt_success_responset>())
    return solver_process.receive_response();
  else
    return response;
}

/// \brief Find all sub expressions of the given \p expr which need to be
///   expressed as separate smt commands.
/// \return A collection of sub expressions, which need to be expressed as
///   separate smt commands. This collection is in traversal order. It will
///   include duplicate subexpressions, which need to be removed by the caller
///   in order to avoid duplicate definitions.
/// \note This pass over \p expr is tightly coupled to the implementation of
///   `convert_expr_to_smt`. This is because any sub expressions which
///   `convert_expr_to_smt` translates into function applications, must also be
///   returned by this`gather_dependent_expressions` function.
static std::vector<exprt> gather_dependent_expressions(const exprt &expr)
{
  std::vector<exprt> dependent_expressions;
  expr.visit_pre([&](const exprt &expr_node) {
    if(can_cast_expr<symbol_exprt>(expr_node))
    {
      dependent_expressions.push_back(expr_node);
    }
  });
  return dependent_expressions;
}

/// \brief Defines any functions which \p expr depends on, which have not yet
///   been defined, along with their dependencies in turn.
void smt2_incremental_decision_proceduret::define_dependent_functions(
  const exprt &expr)
{
  std::unordered_set<exprt, irep_hash> seen_expressions =
    make_range(expression_identifiers)
      .map([](const std::pair<exprt, smt_identifier_termt> &expr_identifier) {
        return expr_identifier.first;
      });
  std::stack<exprt> to_be_defined;
  const auto push_dependencies_needed = [&](const exprt &expr) {
    bool result = false;
    for(const auto &dependency : gather_dependent_expressions(expr))
    {
      if(!seen_expressions.insert(dependency).second)
        continue;
      result = true;
      to_be_defined.push(dependency);
    }
    return result;
  };
  push_dependencies_needed(expr);
  while(!to_be_defined.empty())
  {
    const exprt current = to_be_defined.top();
    if(push_dependencies_needed(current))
      continue;
    if(const auto symbol_expr = expr_try_dynamic_cast<symbol_exprt>(current))
    {
      const irep_idt &identifier = symbol_expr->get_identifier();
      const symbolt *symbol = nullptr;
      if(ns.lookup(identifier, symbol) || symbol->value.is_nil())
      {
        const smt_declare_function_commandt function{
          smt_identifier_termt(
            identifier, convert_type_to_smt_sort(symbol_expr->type())),
          {}};
        expression_identifiers.emplace(*symbol_expr, function.identifier());
        solver_process->send(function);
      }
      else
      {
        if(push_dependencies_needed(symbol->value))
          continue;
        const smt_define_function_commandt function{
          symbol->name, {}, convert_expr_to_smt(symbol->value)};
        expression_identifiers.emplace(*symbol_expr, function.identifier());
        solver_process->send(function);
      }
    }
    to_be_defined.pop();
  }
}

smt2_incremental_decision_proceduret::smt2_incremental_decision_proceduret(
  const namespacet &_ns,
  std::unique_ptr<smt_base_solver_processt> _solver_process,
  message_handlert &message_handler)
  : ns{_ns},
    number_of_solver_calls{0},
    solver_process(std::move(_solver_process)),
    log{message_handler}
{
  solver_process->send(
    smt_set_option_commandt{smt_option_produce_modelst{true}});
  solver_process->send(smt_set_logic_commandt{
    smt_logic_quantifier_free_uninterpreted_functions_bit_vectorst{}});
}

void smt2_incremental_decision_proceduret::ensure_handle_for_expr_defined(
  const exprt &expr)
{
  if(
    expression_handle_identifiers.find(expr) !=
    expression_handle_identifiers.cend())
  {
    return;
  }

  define_dependent_functions(expr);
  smt_define_function_commandt function{
    "B" + std::to_string(handle_sequence()), {}, convert_expr_to_smt(expr)};
  expression_handle_identifiers.emplace(expr, function.identifier());
  solver_process->send(function);
}

exprt smt2_incremental_decision_proceduret::handle(const exprt &expr)
{
  log.debug() << "`handle`  -\n  " << expr.pretty(2, 0) << messaget::eom;
  ensure_handle_for_expr_defined(expr);
  return expr;
}

exprt smt2_incremental_decision_proceduret::get(const exprt &expr) const
{
  UNIMPLEMENTED_FEATURE("`get` of:\n  " + expr.pretty(2, 0));
}

void smt2_incremental_decision_proceduret::print_assignment(
  std::ostream &out) const
{
  UNIMPLEMENTED_FEATURE("printing of assignments.");
}

std::string
smt2_incremental_decision_proceduret::decision_procedure_text() const
{
  return "incremental SMT2 solving via " + solver_process->description();
}

std::size_t
smt2_incremental_decision_proceduret::get_number_of_solver_calls() const
{
  return number_of_solver_calls;
}

void smt2_incremental_decision_proceduret::set_to(const exprt &expr, bool value)
{
  PRECONDITION(can_cast_type<bool_typet>(expr.type()));
  log.debug() << "`set_to` (" << std::string{value ? "true" : "false"}
              << ") -\n  " << expr.pretty(2, 0) << messaget::eom;

  define_dependent_functions(expr);
  auto converted_term = [&]() -> smt_termt {
    const auto expression_handle_identifier =
      expression_handle_identifiers.find(expr);
    if(expression_handle_identifier != expression_handle_identifiers.cend())
      return expression_handle_identifier->second;
    else
      return convert_expr_to_smt(expr);
  }();
  if(!value)
    converted_term = smt_core_theoryt::make_not(converted_term);
  solver_process->send(smt_assert_commandt{converted_term});
}

void smt2_incremental_decision_proceduret::push(
  const std::vector<exprt> &assumptions)
{
  for(const auto &assumption : assumptions)
  {
    UNIMPLEMENTED_FEATURE(
      "pushing of assumption:\n  " + assumption.pretty(2, 0));
  }
  UNIMPLEMENTED_FEATURE("`push` of empty assumptions.");
}

void smt2_incremental_decision_proceduret::push()
{
  UNIMPLEMENTED_FEATURE("`push`.");
}

void smt2_incremental_decision_proceduret::pop()
{
  UNIMPLEMENTED_FEATURE("`pop`.");
}

NODISCARD
static decision_proceduret::resultt lookup_decision_procedure_result(
  const smt_check_sat_response_kindt &response_kind)
{
  if(response_kind.cast<smt_sat_responset>())
    return decision_proceduret::resultt::D_SATISFIABLE;
  if(response_kind.cast<smt_unsat_responset>())
    return decision_proceduret::resultt::D_UNSATISFIABLE;
  if(response_kind.cast<smt_unknown_responset>())
    return decision_proceduret::resultt::D_ERROR;
  UNREACHABLE;
}

decision_proceduret::resultt smt2_incremental_decision_proceduret::dec_solve()
{
  ++number_of_solver_calls;
  const smt_responset result =
    get_response_to_command(*solver_process, smt_check_sat_commandt{});
  if(const auto check_sat_response = result.cast<smt_check_sat_responset>())
  {
    if(check_sat_response->kind().cast<smt_unknown_responset>())
      log.error() << "SMT2 solver returned \"unknown\"" << messaget::eom;
    return lookup_decision_procedure_result(check_sat_response->kind());
  }
  UNIMPLEMENTED_FEATURE("handling solver response.");
}
