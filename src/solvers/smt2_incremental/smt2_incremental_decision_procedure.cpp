// Author: Diffblue Ltd.

#include "smt2_incremental_decision_procedure.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/expr.h>
#include <util/namespace.h>
#include <util/nodiscard.h>
#include <util/range.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <solvers/smt2_incremental/ast/smt_commands.h>
#include <solvers/smt2_incremental/ast/smt_responses.h>
#include <solvers/smt2_incremental/ast/smt_terms.h>
#include <solvers/smt2_incremental/construct_value_expr_from_smt.h>
#include <solvers/smt2_incremental/convert_expr_to_smt.h>
#include <solvers/smt2_incremental/smt_solver_process.h>
#include <solvers/smt2_incremental/theories/smt_array_theory.h>
#include <solvers/smt2_incremental/theories/smt_core_theory.h>
#include <solvers/smt2_incremental/type_size_mapping.h>

#include <stack>
#include <unordered_set>

/// Issues a command to the solving process which is expected to optionally
/// return a success status followed by the actual response of interest.
static smt_responset get_response_to_command(
  smt_base_solver_processt &solver_process,
  const smt_commandt &command,
  const std::unordered_map<irep_idt, smt_identifier_termt> &identifier_table)
{
  solver_process.send(command);
  auto response = solver_process.receive_response(identifier_table);
  if(response.cast<smt_success_responset>())
    return solver_process.receive_response(identifier_table);
  else
    return response;
}

static optionalt<std::string>
get_problem_messages(const smt_responset &response)
{
  if(const auto error = response.cast<smt_error_responset>())
  {
    return "SMT solver returned an error message - " +
           id2string(error->message());
  }
  if(response.cast<smt_unsupported_responset>())
  {
    return {"SMT solver does not support given command."};
  }
  return {};
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
/// \details `symbol_exprt`, `array_exprt` and `nondet_symbol_exprt` add
///   dependant expressions.
static std::vector<exprt> gather_dependent_expressions(const exprt &expr)
{
  std::vector<exprt> dependent_expressions;
  expr.visit_pre([&](const exprt &expr_node) {
    if(
      can_cast_expr<symbol_exprt>(expr_node) ||
      can_cast_expr<array_exprt>(expr_node) ||
      can_cast_expr<array_of_exprt>(expr_node) ||
      can_cast_expr<nondet_symbol_exprt>(expr_node))
    {
      dependent_expressions.push_back(expr_node);
    }
  });
  return dependent_expressions;
}

void smt2_incremental_decision_proceduret::initialize_array_elements(
  const array_exprt &array,
  const smt_identifier_termt &array_identifier)
{
  identifier_table.emplace(array_identifier.identifier(), array_identifier);
  const std::vector<exprt> &elements = array.operands();
  const typet &index_type = array.type().index_type();
  for(std::size_t i = 0; i < elements.size(); ++i)
  {
    const smt_termt index = convert_expr_to_smt(from_integer(i, index_type));
    const smt_assert_commandt element_definition{smt_core_theoryt::equal(
      smt_array_theoryt::select(array_identifier, index),
      convert_expr_to_smt(elements.at(i)))};
    solver_process->send(element_definition);
  }
}

void smt2_incremental_decision_proceduret::initialize_array_elements(
  const array_of_exprt &array,
  const smt_identifier_termt &array_identifier)
{
  const smt_sortt index_type =
    convert_type_to_smt_sort(array.type().index_type());
  const smt_identifier_termt array_index_identifier{
    id2string(array_identifier.identifier()) + "_index", index_type};
  const smt_termt element_value = convert_expr_to_smt(array.what());

  const smt_assert_commandt elements_definition{smt_forall_termt{
    {array_index_identifier},
    smt_core_theoryt::equal(
      smt_array_theoryt::select(array_identifier, array_index_identifier),
      element_value)}};
  solver_process->send(elements_definition);
}

template <typename t_exprt>
void smt2_incremental_decision_proceduret::define_array_function(
  const t_exprt &array)
{
  const smt_sortt array_sort = convert_type_to_smt_sort(array.type());
  INVARIANT(
    array_sort.cast<smt_array_sortt>(),
    "Converting array typed expression to SMT should result in a term of array "
    "sort.");
  const smt_identifier_termt array_identifier{
    "array_" + std::to_string(array_sequence()), array_sort};
  solver_process->send(smt_declare_function_commandt{array_identifier, {}});
  initialize_array_elements(array, array_identifier);
  expression_identifiers.emplace(array, array_identifier);
}

void send_function_definition(
  const exprt &expr,
  const irep_idt &symbol_identifier,
  const std::unique_ptr<smt_base_solver_processt> &solver_process,
  std::unordered_map<exprt, smt_identifier_termt, irep_hash>
    &expression_identifiers,
  std::unordered_map<irep_idt, smt_identifier_termt> &identifier_table)
{
  const smt_declare_function_commandt function{
    smt_identifier_termt(
      symbol_identifier, convert_type_to_smt_sort(expr.type())),
    {}};
  expression_identifiers.emplace(expr, function.identifier());
  identifier_table.emplace(symbol_identifier, function.identifier());
  solver_process->send(function);
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
        send_function_definition(
          *symbol_expr,
          symbol_expr->get_identifier(),
          solver_process,
          expression_identifiers,
          identifier_table);
      }
      else
      {
        if(push_dependencies_needed(symbol->value))
          continue;
        const smt_define_function_commandt function{
          symbol->name, {}, convert_expr_to_smt(symbol->value)};
        expression_identifiers.emplace(*symbol_expr, function.identifier());
        identifier_table.emplace(identifier, function.identifier());
        solver_process->send(function);
      }
    }
    else if(const auto array_expr = expr_try_dynamic_cast<array_exprt>(current))
      define_array_function(*array_expr);
    else if(
      const auto array_of_expr = expr_try_dynamic_cast<array_of_exprt>(current))
    {
      define_array_function(*array_of_expr);
    }
    else if(
      const auto nondet_symbol =
        expr_try_dynamic_cast<nondet_symbol_exprt>(current))
    {
      send_function_definition(
        *nondet_symbol,
        nondet_symbol->get_identifier(),
        solver_process,
        expression_identifiers,
        identifier_table);
    }
    to_be_defined.pop();
  }
}

/// Replaces the sub expressions of \p expr which have been defined as separate
/// functions in the smt solver, using the \p expression_identifiers map.
static exprt substitute_identifiers(
  exprt expr,
  const std::unordered_map<exprt, smt_identifier_termt, irep_hash>
    &expression_identifiers)
{
  expr.visit_pre([&](exprt &node) -> void {
    auto find_result = expression_identifiers.find(node);
    if(find_result == expression_identifiers.cend())
      return;
    const auto type = find_result->first.type();
    node = symbol_exprt{find_result->second.identifier(), type};
  });
  return expr;
}

smt2_incremental_decision_proceduret::smt2_incremental_decision_proceduret(
  const namespacet &_ns,
  std::unique_ptr<smt_base_solver_processt> _solver_process,
  message_handlert &message_handler)
  : ns{_ns},
    number_of_solver_calls{0},
    solver_process(std::move(_solver_process)),
    log{message_handler},
    object_map{initial_smt_object_map()}
{
  solver_process->send(
    smt_set_option_commandt{smt_option_produce_modelst{true}});
  solver_process->send(smt_set_logic_commandt{smt_logic_allt{}});
  solver_process->send(object_size_function.declaration);
  solver_process->send(is_dynamic_object_function.declaration);
}

void smt2_incremental_decision_proceduret::ensure_handle_for_expr_defined(
  const exprt &in_expr)
{
  if(
    expression_handle_identifiers.find(in_expr) !=
    expression_handle_identifiers.cend())
  {
    return;
  }

  const exprt lowered_expr = lower_byte_operators(in_expr, ns);

  define_dependent_functions(lowered_expr);
  smt_define_function_commandt function{
    "B" + std::to_string(handle_sequence()),
    {},
    convert_expr_to_smt(lowered_expr)};
  expression_handle_identifiers.emplace(in_expr, function.identifier());
  identifier_table.emplace(
    function.identifier().identifier(), function.identifier());
  solver_process->send(function);
}

void smt2_incremental_decision_proceduret::define_index_identifiers(
  const exprt &expr)
{
  expr.visit_pre([&](const exprt &expr_node) {
    if(!can_cast_type<array_typet>(expr_node.type()))
      return;
    if(const auto with_expr = expr_try_dynamic_cast<with_exprt>(expr_node))
    {
      for(auto operand_ite = ++with_expr->operands().begin();
          operand_ite != with_expr->operands().end();
          operand_ite += 2)
      {
        const auto index_expr = *operand_ite;
        const auto index_term = convert_expr_to_smt(index_expr);
        const auto index_identifier =
          "index_" + std::to_string(index_sequence());
        const auto index_definition =
          smt_define_function_commandt{index_identifier, {}, index_term};
        expression_identifiers.emplace(
          index_expr, index_definition.identifier());
        identifier_table.emplace(
          index_identifier, index_definition.identifier());
        solver_process->send(
          smt_define_function_commandt{index_identifier, {}, index_term});
      }
    }
  });
}

smt_termt
smt2_incremental_decision_proceduret::convert_expr_to_smt(const exprt &expr)
{
  define_index_identifiers(expr);
  const exprt substituted =
    substitute_identifiers(expr, expression_identifiers);
  track_expression_objects(substituted, ns, object_map);
  associate_pointer_sizes(
    substituted,
    ns,
    pointer_sizes_map,
    object_map,
    object_size_function.make_application,
    is_dynamic_object_function.make_application);
  return ::convert_expr_to_smt(
    substituted,
    object_map,
    pointer_sizes_map,
    object_size_function.make_application,
    is_dynamic_object_function.make_application);
}

exprt smt2_incremental_decision_proceduret::handle(const exprt &expr)
{
  log.conditional_output(log.debug(), [&](messaget::mstreamt &debug) {
    debug << "`handle`  -\n  " << expr.pretty(2, 0) << messaget::eom;
  });
  ensure_handle_for_expr_defined(expr);
  return expr;
}

static optionalt<smt_termt> get_identifier(
  const exprt &expr,
  const std::unordered_map<exprt, smt_identifier_termt, irep_hash>
    &expression_handle_identifiers,
  const std::unordered_map<exprt, smt_identifier_termt, irep_hash>
    &expression_identifiers)
{
  const auto handle_find_result = expression_handle_identifiers.find(expr);
  if(handle_find_result != expression_handle_identifiers.cend())
    return handle_find_result->second;
  const auto expr_find_result = expression_identifiers.find(expr);
  if(expr_find_result != expression_identifiers.cend())
    return expr_find_result->second;
  return {};
}

array_exprt smt2_incremental_decision_proceduret::get_expr(
  const smt_termt &array,
  const array_typet &type) const
{
  INVARIANT(
    type.is_complete(), "Array size is required for getting array values.");
  const auto size = numeric_cast<std::size_t>(get(type.size()));
  INVARIANT(
    size,
    "Size of array must be convertible to std::size_t for getting array value");
  std::vector<exprt> elements;
  const auto index_type = type.index_type();
  elements.reserve(*size);
  for(std::size_t index = 0; index < size; ++index)
  {
    elements.push_back(get_expr(
      smt_array_theoryt::select(
        array,
        ::convert_expr_to_smt(
          from_integer(index, index_type),
          object_map,
          pointer_sizes_map,
          object_size_function.make_application,
          is_dynamic_object_function.make_application)),
      type.element_type()));
  }
  return array_exprt{elements, type};
}

exprt smt2_incremental_decision_proceduret::get_expr(
  const smt_termt &descriptor,
  const typet &type) const
{
  const smt_get_value_commandt get_value_command{descriptor};
  const smt_responset response = get_response_to_command(
    *solver_process, get_value_command, identifier_table);
  const auto get_value_response = response.cast<smt_get_value_responset>();
  if(!get_value_response)
  {
    throw analysis_exceptiont{
      "Expected get-value response from solver, but received - " +
      response.pretty()};
  }
  if(get_value_response->pairs().size() > 1)
  {
    throw analysis_exceptiont{
      "Expected single valuation pair in get-value response from solver, but "
      "received multiple pairs - " +
      response.pretty()};
  }
  return construct_value_expr_from_smt(
    get_value_response->pairs()[0].get().value(), type);
}

exprt smt2_incremental_decision_proceduret::get(const exprt &expr) const
{
  log.conditional_output(log.debug(), [&](messaget::mstreamt &debug) {
    debug << "`get` - \n  " + expr.pretty(2, 0) << messaget::eom;
  });
  auto descriptor = [&]() -> optionalt<smt_termt> {
    if(const auto index_expr = expr_try_dynamic_cast<index_exprt>(expr))
    {
      const auto array = get_identifier(
        index_expr->array(),
        expression_handle_identifiers,
        expression_identifiers);
      const auto index = get_identifier(
        index_expr->index(),
        expression_handle_identifiers,
        expression_identifiers);
      if(!array || !index)
        return {};
      return smt_array_theoryt::select(*array, *index);
    }
    return get_identifier(
      expr, expression_handle_identifiers, expression_identifiers);
  }();
  if(!descriptor)
  {
    if(gather_dependent_expressions(expr).empty())
    {
      INVARIANT(
        objects_are_already_tracked(expr, object_map),
        "Objects in expressions being read should already be tracked from "
        "point of being set/handled.");
      descriptor = ::convert_expr_to_smt(
        expr,
        object_map,
        pointer_sizes_map,
        object_size_function.make_application,
        is_dynamic_object_function.make_application);
    }
    else
    {
      const auto symbol_expr = expr_try_dynamic_cast<symbol_exprt>(expr);
      INVARIANT(
        symbol_expr, "Unhandled expressions are expected to be symbols");
      // Note this case is currently expected to be encountered during trace
      // generation for -
      //  * Steps which were removed via --slice-formula.
      //  * Getting concurrency clock values.
      // The below implementation which returns the given expression was chosen
      // based on the implementation of `smt2_convt::get` in the non-incremental
      // smt2 decision procedure.
      log.warning()
        << "`get` attempted for unknown symbol, with identifier - \n"
        << symbol_expr->get_identifier() << messaget::eom;
      return expr;
    }
  }
  if(const auto array_type = type_try_dynamic_cast<array_typet>(expr.type()))
  {
    if(array_type->is_incomplete())
      return expr;
    return get_expr(*descriptor, *array_type);
  }
  return get_expr(*descriptor, expr.type());
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

void smt2_incremental_decision_proceduret::set_to(
  const exprt &in_expr,
  bool value)
{
  const exprt lowered_expr = lower_byte_operators(in_expr, ns);
  PRECONDITION(can_cast_type<bool_typet>(lowered_expr.type()));
  log.conditional_output(log.debug(), [&](messaget::mstreamt &debug) {
    debug << "`set_to` (" << std::string{value ? "true" : "false"} << ") -\n  "
          << lowered_expr.pretty(2, 0) << messaget::eom;
  });

  define_dependent_functions(lowered_expr);
  auto converted_term = [&]() -> smt_termt {
    const auto expression_handle_identifier =
      expression_handle_identifiers.find(lowered_expr);
    if(expression_handle_identifier != expression_handle_identifiers.cend())
      return expression_handle_identifier->second;
    else
      return convert_expr_to_smt(lowered_expr);
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

void smt2_incremental_decision_proceduret::define_object_properties()
{
  object_properties_defined.resize(object_map.size());
  for(const auto &key_value : object_map)
  {
    const decision_procedure_objectt &object = key_value.second;
    if(object_properties_defined[object.unique_id])
      continue;
    else
      object_properties_defined[object.unique_id] = true;
    define_dependent_functions(object.size);
    solver_process->send(object_size_function.make_definition(
      object.unique_id, convert_expr_to_smt(object.size)));
    solver_process->send(is_dynamic_object_function.make_definition(
      object.unique_id, object.is_dynamic));
  }
}

decision_proceduret::resultt smt2_incremental_decision_proceduret::dec_solve()
{
  ++number_of_solver_calls;
  define_object_properties();
  const smt_responset result = get_response_to_command(
    *solver_process, smt_check_sat_commandt{}, identifier_table);
  if(const auto check_sat_response = result.cast<smt_check_sat_responset>())
  {
    if(check_sat_response->kind().cast<smt_unknown_responset>())
      log.error() << "SMT2 solver returned \"unknown\"" << messaget::eom;
    return lookup_decision_procedure_result(check_sat_response->kind());
  }
  if(const auto problem = get_problem_messages(result))
    throw analysis_exceptiont{*problem};
  throw analysis_exceptiont{"Unexpected kind of response from SMT solver."};
}
