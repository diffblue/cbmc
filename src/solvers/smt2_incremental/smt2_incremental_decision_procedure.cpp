// Author: Diffblue Ltd.

#include "smt2_incremental_decision_procedure.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/range.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/string_constant.h>

#include <solvers/smt2_incremental/ast/smt_commands.h>
#include <solvers/smt2_incremental/ast/smt_responses.h>
#include <solvers/smt2_incremental/ast/smt_terms.h>
#include <solvers/smt2_incremental/construct_value_expr_from_smt.h>
#include <solvers/smt2_incremental/convert_expr_to_smt.h>
#include <solvers/smt2_incremental/encoding/enum_encoding.h>
#include <solvers/smt2_incremental/encoding/nondet_padding.h>
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

/// Returns a message string describing the problem in the case where the
/// response from the solver is an error status. Returns empty otherwise.
static std::optional<std::string>
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
static std::vector<exprt> gather_dependent_expressions(const exprt &root_expr)
{
  std::vector<exprt> dependent_expressions;

  std::stack<const exprt *> stack;
  stack.push(&root_expr);

  while(!stack.empty())
  {
    const exprt &expr_node = *stack.top();
    stack.pop();
    if(
      can_cast_expr<symbol_exprt>(expr_node) ||
      can_cast_expr<array_exprt>(expr_node) ||
      can_cast_expr<array_of_exprt>(expr_node) ||
      can_cast_expr<nondet_symbol_exprt>(expr_node) ||
      can_cast_expr<string_constantt>(expr_node))
    {
      dependent_expressions.push_back(expr_node);
    }
    // The decision procedure does not depend on the values inside address of
    // code typed expressions. We can build the address without knowing the
    // value at that memory location. In this case the hypothetical compiled
    // machine instructions at the address are not relevant to solving, only
    // representing *which* function a pointer points to is needed.
    const auto address_of = expr_try_dynamic_cast<address_of_exprt>(expr_node);
    if(address_of && can_cast_type<code_typet>(address_of->object().type()))
      continue;
    for(auto &operand : expr_node.operands())
      stack.push(&operand);
  }
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

void smt2_incremental_decision_proceduret::initialize_array_elements(
  const string_constantt &string,
  const smt_identifier_termt &array_identifier)
{
  initialize_array_elements(string.to_array_expr(), array_identifier);
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
      send_function_definition(
        *symbol_expr,
        symbol_expr->get_identifier(),
        solver_process,
        expression_identifiers,
        identifier_table);
    }
    else if(const auto array_expr = expr_try_dynamic_cast<array_exprt>(current))
      define_array_function(*array_expr);
    else if(
      const auto array_of_expr = expr_try_dynamic_cast<array_of_exprt>(current))
    {
      define_array_function(*array_of_expr);
    }
    else if(
      const auto string = expr_try_dynamic_cast<string_constantt>(current))
    {
      define_array_function(*string);
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
    object_map{initial_smt_object_map()},
    struct_encoding{_ns}
{
  solver_process->send(
    smt_set_option_commandt{smt_option_produce_modelst{true}});
  solver_process->send(smt_set_logic_commandt{smt_logic_allt{}});
  solver_process->send(object_size_function.declaration);
  solver_process->send(is_dynamic_object_function.declaration);
}

static exprt lower_rw_ok_pointer_in_range(exprt expr, const namespacet &ns)
{
  expr.visit_pre([&ns](exprt &expr) {
    if(
      auto prophecy_r_or_w_ok =
        expr_try_dynamic_cast<prophecy_r_or_w_ok_exprt>(expr))
    {
      expr = simplify_expr(prophecy_r_or_w_ok->lower(ns), ns);
    }
    else if(
      auto prophecy_pointer_in_range =
        expr_try_dynamic_cast<prophecy_pointer_in_range_exprt>(expr))
    {
      expr = simplify_expr(prophecy_pointer_in_range->lower(ns), ns);
    }
  });
  return expr;
}

static exprt lower_zero_extend(exprt expr, const namespacet &ns)
{
  expr.visit_pre([](exprt &expr) {
    if(auto zero_extend = expr_try_dynamic_cast<zero_extend_exprt>(expr))
    {
      expr = zero_extend->lower();
    }
  });
  return expr;
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

  const exprt lowered_expr = lower(in_expr);

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

exprt smt2_incremental_decision_proceduret::substitute_defined_padding(
  exprt root_expr)
{
  root_expr.visit_pre([&](exprt &node) {
    if(const auto pad = expr_try_dynamic_cast<nondet_padding_exprt>(node))
    {
      const auto instance = "padding_" + std::to_string(padding_sequence());
      const auto term =
        smt_identifier_termt{instance, convert_type_to_smt_sort(pad->type())};
      solver_process->send(smt_declare_function_commandt{term, {}});
      node = symbol_exprt{instance, node.type()};
    }
  });
  return root_expr;
}

smt_termt
smt2_incremental_decision_proceduret::convert_expr_to_smt(const exprt &expr)
{
  define_index_identifiers(expr);
  const exprt substituted = substitute_defined_padding(
    substitute_identifiers(expr, expression_identifiers));
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

std::optional<smt_termt>
smt2_incremental_decision_proceduret::get_identifier(const exprt &expr) const
{
  // Lookup the non-lowered form first.
  const auto handle_find_result = expression_handle_identifiers.find(expr);
  if(handle_find_result != expression_handle_identifiers.cend())
    return handle_find_result->second;
  const auto expr_find_result = expression_identifiers.find(expr);
  if(expr_find_result != expression_identifiers.cend())
    return expr_find_result->second;

  // If that didn't yield any results, then try the lowered form.
  const exprt lowered_expr = lower(expr);
  const auto lowered_handle_find_result =
    expression_handle_identifiers.find(lowered_expr);
  if(lowered_handle_find_result != expression_handle_identifiers.cend())
    return lowered_handle_find_result->second;
  const auto lowered_expr_find_result =
    expression_identifiers.find(lowered_expr);
  if(lowered_expr_find_result != expression_identifiers.cend())
    return lowered_expr_find_result->second;
  return {};
}

std::optional<exprt> smt2_incremental_decision_proceduret::get_expr(
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
    const auto index_term = ::convert_expr_to_smt(
      from_integer(index, index_type),
      object_map,
      pointer_sizes_map,
      object_size_function.make_application,
      is_dynamic_object_function.make_application);
    auto element = get_expr(
      smt_array_theoryt::select(array, index_term), type.element_type());
    if(!element)
      return {};
    elements.push_back(std::move(*element));
  }
  return array_exprt{elements, type};
}

std::optional<exprt> smt2_incremental_decision_proceduret::get_expr(
  const smt_termt &struct_term,
  const struct_tag_typet &type) const
{
  const auto encoded_result =
    get_expr(struct_term, struct_encoding.encode(type));
  if(!encoded_result)
    return {};
  return {struct_encoding.decode(*encoded_result, type)};
}

std::optional<exprt> smt2_incremental_decision_proceduret::get_expr(
  const smt_termt &union_term,
  const union_tag_typet &type) const
{
  const auto encoded_result =
    get_expr(union_term, struct_encoding.encode(type));
  if(!encoded_result)
    return {};
  return {struct_encoding.decode(*encoded_result, type)};
}

std::optional<exprt> smt2_incremental_decision_proceduret::get_expr(
  const smt_termt &descriptor,
  const typet &type) const
{
  if(const auto array_type = type_try_dynamic_cast<array_typet>(type))
  {
    if(array_type->is_incomplete())
      return {};
    return get_expr(descriptor, *array_type);
  }
  if(const auto struct_type = type_try_dynamic_cast<struct_tag_typet>(type))
  {
    return get_expr(descriptor, *struct_type);
  }
  if(const auto union_type = type_try_dynamic_cast<union_tag_typet>(type))
  {
    return get_expr(descriptor, *union_type);
  }
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
    get_value_response->pairs()[0].get().value(), type, ns);
}

// This is a fall back which builds resulting expression based on getting the
// values of its operands. It is used during trace building in the case where
// certain kinds of expression appear on the left hand side of an
// assignment. For example in the following trace assignment -
//   `byte_extract_little_endian(x, offset) = 1`
// `::get` will be called on `byte_extract_little_endian(x, offset)` and
// we build a resulting expression where `x` and `offset` are substituted
// with their values.
static exprt build_expr_based_on_getting_operands(
  const exprt &expr,
  const stack_decision_proceduret &decision_procedure)
{
  exprt copy = expr;
  for(auto &op : copy.operands())
  {
    exprt eval_op = decision_procedure.get(op);
    if(eval_op.is_nil())
      return nil_exprt{};
    op = std::move(eval_op);
  }
  return copy;
}

exprt smt2_incremental_decision_proceduret::get(const exprt &expr) const
{
  log.conditional_output(log.debug(), [&](messaget::mstreamt &debug) {
    debug << "`get` - \n  " + expr.pretty(2, 0) << messaget::eom;
  });
  auto descriptor = [&]() -> std::optional<smt_termt> {
    if(const auto index_expr = expr_try_dynamic_cast<index_exprt>(expr))
    {
      const auto array = get_identifier(index_expr->array());
      const auto index = get_identifier(index_expr->index());
      if(!array || !index)
        return {};
      return smt_array_theoryt::select(*array, *index);
    }
    if(auto identifier_descriptor = get_identifier(expr))
    {
      return identifier_descriptor;
    }
    const exprt lowered = lower(expr);
    if(gather_dependent_expressions(lowered).empty())
    {
      INVARIANT(
        objects_are_already_tracked(lowered, object_map),
        "Objects in expressions being read should already be tracked from "
        "point of being set/handled.");
      return ::convert_expr_to_smt(
        lowered,
        object_map,
        pointer_sizes_map,
        object_size_function.make_application,
        is_dynamic_object_function.make_application);
    }
    return {};
  }();
  if(!descriptor)
  {
    INVARIANT_WITH_DIAGNOSTICS(
      !can_cast_expr<symbol_exprt>(expr),
      "symbol expressions must have a known value",
      irep_pretty_diagnosticst{expr});
    return build_expr_based_on_getting_operands(expr, *this);
  }
  if(auto result = get_expr(*descriptor, expr.type()))
    return std::move(*result);
  return expr;
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
  log.conditional_output(log.debug(), [&](messaget::mstreamt &debug) {
    debug << "`set_to` (" << std::string{value ? "true" : "false"} << ") -\n  "
          << in_expr.pretty(2, 0) << messaget::eom;
  });
  const exprt lowered_expr = lower(in_expr);
  PRECONDITION(can_cast_type<bool_typet>(lowered_expr.type()));

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

[[nodiscard]] static decision_proceduret::resultt
lookup_decision_procedure_result(
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

exprt smt2_incremental_decision_proceduret::lower(exprt expression) const
{
  const exprt lowered = struct_encoding.encode(lower_zero_extend(
    lower_enum(
      lower_byte_operators(lower_rw_ok_pointer_in_range(expression, ns), ns),
      ns),
    ns));
  log.conditional_output(log.debug(), [&](messaget::mstreamt &debug) {
    if(lowered != expression)
      debug << "lowered to -\n  " << lowered.pretty(2, 0) << messaget::eom;
  });
  return lowered;
}

decision_proceduret::resultt
smt2_incremental_decision_proceduret::dec_solve(const exprt &assumption)
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
