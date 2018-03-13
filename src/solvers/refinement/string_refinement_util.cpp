/*******************************************************************\

 Module: String solver

 Author: Diffblue Ltd.

\*******************************************************************/

#include <algorithm>
#include <numeric>
#include <functional>
#include <iostream>
#include <util/arith_tools.h>
#include <util/ssa_expr.h>
#include <util/std_expr.h>
#include <util/expr_iterator.h>
#include <util/graph.h>
#include <util/magic.h>
#include <util/make_unique.h>
#include "string_refinement_util.h"

/// Get the valuation of the string, given a valuation
static optionalt<std::vector<mp_integer>> eval_string(
  const array_string_exprt &a,
  const std::function<exprt(const exprt &)> &get_value);

/// Make a string from a constant array
static array_string_exprt make_string(
  const std::vector<mp_integer> &array,
  const array_typet &array_type);

bool is_char_type(const typet &type)
{
  return type.id() == ID_unsignedbv &&
         to_unsignedbv_type(type).get_width() <=
           STRING_REFINEMENT_MAX_CHAR_WIDTH;
}

bool is_char_array_type(const typet &type, const namespacet &ns)
{
  if(type.id() == ID_symbol)
    return is_char_array_type(ns.follow(type), ns);
  return type.id() == ID_array && is_char_type(type.subtype());
}

bool is_char_pointer_type(const typet &type)
{
  return type.id() == ID_pointer && is_char_type(type.subtype());
}

bool has_subtype(
  const typet &type,
  const std::function<bool(const typet &)> &pred)
{
  if(pred(type))
    return true;

  if(type.id() == ID_struct || type.id() == ID_union)
  {
    const struct_union_typet &struct_type = to_struct_union_type(type);
    return std::any_of(
      struct_type.components().begin(),
      struct_type.components().end(), // NOLINTNEXTLINE
      [&](const struct_union_typet::componentt &comp) {
        return has_subtype(comp.type(), pred);
      });
  }

  return std::any_of( // NOLINTNEXTLINE
    type.subtypes().begin(), type.subtypes().end(), [&](const typet &t) {
      return has_subtype(t, pred);
    });
}

bool has_char_pointer_subtype(const typet &type)
{
  return has_subtype(type, is_char_pointer_type);
}

bool has_string_subtype(const typet &type)
{
  // NOLINTNEXTLINE
  return has_subtype(
    type, [](const typet &subtype) { return subtype == string_typet(); });
}

bool has_char_array_subexpr(const exprt &expr, const namespacet &ns)
{
  const auto it = std::find_if(
    expr.depth_begin(), expr.depth_end(), [&](const exprt &e) { // NOLINT
      return is_char_array_type(e.type(), ns);
    });
  return it != expr.depth_end();
}

sparse_arrayt::sparse_arrayt(const with_exprt &expr)
{
  auto ref = std::ref(static_cast<const exprt &>(expr));
  while(can_cast_expr<with_exprt>(ref.get()))
  {
    const auto &with_expr = expr_dynamic_cast<with_exprt>(ref.get());
    const auto current_index = numeric_cast_v<std::size_t>(with_expr.where());
    entries.emplace_back(current_index, with_expr.new_value());
    ref = with_expr.old();
  }

  // This function only handles 'with' and 'array_of' expressions
  PRECONDITION(ref.get().id() == ID_array_of);
  default_value = expr_dynamic_cast<array_of_exprt>(ref.get()).what();
}

exprt sparse_arrayt::to_if_expression(const exprt &index) const
{
  return std::accumulate(
    entries.begin(),
    entries.end(),
    default_value,
    [&](
      const exprt if_expr,
      const std::pair<std::size_t, exprt> &entry) { // NOLINT
      const exprt entry_index = from_integer(entry.first, index.type());
      const exprt &then_expr = entry.second;
      CHECK_RETURN(then_expr.type() == if_expr.type());
      const equal_exprt index_equal(index, entry_index);
      return if_exprt(index_equal, then_expr, if_expr, if_expr.type());
    });
}

interval_sparse_arrayt::interval_sparse_arrayt(const with_exprt &expr)
  : sparse_arrayt(expr)
{
  // Entries are sorted so that successive entries correspond to intervals
  std::sort(
    entries.begin(),
    entries.end(),
    [](
      const std::pair<std::size_t, exprt> &a,
      const std::pair<std::size_t, exprt> &b) { return a.first < b.first; });
}

exprt interval_sparse_arrayt::to_if_expression(const exprt &index) const
{
  return std::accumulate(
    entries.rbegin(),
    entries.rend(),
    default_value,
    [&](
      const exprt if_expr,
      const std::pair<std::size_t, exprt> &entry) { // NOLINT
      const exprt entry_index = from_integer(entry.first, index.type());
      const exprt &then_expr = entry.second;
      CHECK_RETURN(then_expr.type() == if_expr.type());
      const binary_relation_exprt index_small_eq(index, ID_le, entry_index);
      return if_exprt(index_small_eq, then_expr, if_expr, if_expr.type());
    });
}

void equation_symbol_mappingt::add(const std::size_t i, const exprt &expr)
{
  equations_containing[expr].push_back(i);
  strings_in_equation[i].push_back(expr);
}

std::vector<exprt>
equation_symbol_mappingt::find_expressions(const std::size_t i)
{
  return strings_in_equation[i];
}

std::vector<std::size_t>
equation_symbol_mappingt::find_equations(const exprt &expr)
{
  return equations_containing[expr];
}

string_transformation_builtin_functiont::
  string_transformation_builtin_functiont(
    const std::vector<exprt> &fun_args,
    array_poolt &array_pool)
{
  PRECONDITION(fun_args.size() > 2);
  const auto arg1 = expr_checked_cast<struct_exprt>(fun_args[2]);
  input = array_pool.find(arg1.op1(), arg1.op0());
  result = array_pool.find(fun_args[1], fun_args[0]);
  args.insert(args.end(), fun_args.begin() + 3, fun_args.end());
}

optionalt<exprt> string_transformation_builtin_functiont::eval(
  const std::function<exprt(const exprt &)> &get_value) const
{
  const auto &input_value = eval_string(input, get_value);
  if(!input_value.has_value())
    return {};

  std::vector<mp_integer> arg_values;
  const auto &insert = std::back_inserter(arg_values);
  const mp_integer unknown('?');
  std::transform(
    args.begin(), args.end(), insert, [&](const exprt &e) { // NOLINT
      if(const auto val = numeric_cast<mp_integer>(get_value(e)))
        return *val;
      INVARIANT(
        get_value(e).id() == ID_unknown,
        "array valuation should only contain constants and unknown");
      return unknown;
    });

  const auto result_value = eval(*input_value, arg_values);
  const auto length = from_integer(result_value.size(), result.length().type());
  const array_typet type(result.type().subtype(), length);
  return make_string(result_value, type);
}

string_insertion_builtin_functiont::string_insertion_builtin_functiont(
  const std::vector<exprt> &fun_args,
  array_poolt &array_pool)
{
  PRECONDITION(fun_args.size() > 4);
  const auto arg1 = expr_checked_cast<struct_exprt>(fun_args[2]);
  input1 = array_pool.find(arg1.op1(), arg1.op0());
  const auto arg2 = expr_checked_cast<struct_exprt>(fun_args[4]);
  input2 = array_pool.find(arg2.op1(), arg2.op0());
  result = array_pool.find(fun_args[1], fun_args[0]);
  args.push_back(fun_args[3]);
  args.insert(args.end(), fun_args.begin() + 5, fun_args.end());
}

string_concatenation_builtin_functiont::string_concatenation_builtin_functiont(
  const std::vector<exprt> &fun_args,
  array_poolt &array_pool)
{
  PRECONDITION(fun_args.size() >= 4 && fun_args.size() <= 6);
  const auto arg1 = expr_checked_cast<struct_exprt>(fun_args[2]);
  input1 = array_pool.find(arg1.op1(), arg1.op0());
  const auto arg2 = expr_checked_cast<struct_exprt>(fun_args[3]);
  input2 = array_pool.find(arg2.op1(), arg2.op0());
  result = array_pool.find(fun_args[1], fun_args[0]);
  args.insert(args.end(), fun_args.begin() + 4, fun_args.end());
}

optionalt<std::vector<mp_integer>> eval_string(
  const array_string_exprt &a,
  const std::function<exprt(const exprt &)> &get_value)
{
  if(a.id() == ID_if)
  {
    const if_exprt &ite = to_if_expr(a);
    const exprt cond = get_value(ite.cond());
    if(!cond.is_constant())
      return {};
    return cond.is_true()
             ? eval_string(to_array_string_expr(ite.true_case()), get_value)
             : eval_string(to_array_string_expr(ite.false_case()), get_value);
  }

  const auto size = numeric_cast<std::size_t>(get_value(a.length()));
  const exprt content = get_value(a.content());
  const auto &array = expr_try_dynamic_cast<array_exprt>(content);
  if(!size || !array)
    return {};

  const auto &ops = array->operands();
  INVARIANT(*size == ops.size(), "operands size should match string size");

  std::vector<mp_integer> result;
  const mp_integer unknown('?');
  const auto &insert = std::back_inserter(result);
  std::transform(
    ops.begin(), ops.end(), insert, [unknown](const exprt &e) { // NOLINT
      if(const auto i = numeric_cast<mp_integer>(e))
        return *i;
      return unknown;
    });
  return result;
}

array_string_exprt
make_string(const std::vector<mp_integer> &array, const array_typet &array_type)
{
  const typet &char_type = array_type.subtype();
  array_exprt array_expr(array_type);
  const auto &insert = std::back_inserter(array_expr.operands());
  std::transform(
    array.begin(), array.end(), insert, [&](const mp_integer &i) { // NOLINT
      return from_integer(i, char_type);
    });
  return to_array_string_expr(array_expr);
}

std::vector<mp_integer> string_concatenation_builtin_functiont::eval(
  const std::vector<mp_integer> &input1_value,
  const std::vector<mp_integer> &input2_value,
  const std::vector<mp_integer> &args_value) const
{
  const std::size_t start_index =
    args_value.size() > 0 && args_value[0] > 0 ? args_value[0].to_ulong() : 0;
  const std::size_t end_index = args_value.size() > 1 && args_value[1] > 0
                                  ? args_value[1].to_ulong()
                                  : input2_value.size();

  std::vector<mp_integer> result(input1_value);
  result.insert(
    result.end(),
    input2_value.begin() + start_index,
    input2_value.begin() + end_index);
  return result;
}

std::vector<mp_integer> string_concat_char_builtin_functiont::eval(
  const std::vector<mp_integer> &input_value,
  const std::vector<mp_integer> &args_value) const
{
  PRECONDITION(args_value.size() == 1);
  std::vector<mp_integer> result(input_value);
  result.push_back(args_value[0]);
  return result;
}

std::vector<mp_integer> string_insertion_builtin_functiont::eval(
  const std::vector<mp_integer> &input1_value,
  const std::vector<mp_integer> &input2_value,
  const std::vector<mp_integer> &args_value) const
{
  PRECONDITION(args_value.size() >= 1 || args_value.size() <= 3);
  const std::size_t &offset = numeric_cast_v<std::size_t>(args_value[0]);
  const std::size_t &start =
    args_value.size() > 1 ? numeric_cast_v<std::size_t>(args_value[1]) : 0;
  const std::size_t &end = args_value.size() > 2
                             ? numeric_cast_v<std::size_t>(args_value[2])
                             : input2_value.size();

  std::vector<mp_integer> result(input1_value);
  result.insert(
    result.begin() + offset,
    input2_value.begin() + start,
    input2_value.end() + end);
  return result;
}

optionalt<exprt> string_insertion_builtin_functiont::eval(
  const std::function<exprt(const exprt &)> &get_value) const
{
  const auto &input1_value = eval_string(input1, get_value);
  const auto &input2_value = eval_string(input2, get_value);
  if(!input2_value.has_value() || !input1_value.has_value())
    return {};

  std::vector<mp_integer> arg_values;
  const auto &insert = std::back_inserter(arg_values);
  const mp_integer unknown('?');
  std::transform(
    args.begin(), args.end(), insert, [&](const exprt &e) { // NOLINT
      if(const auto val = numeric_cast<mp_integer>(get_value(e)))
        return *val;
      return unknown;
    });

  const auto result_value = eval(*input1_value, *input2_value, arg_values);
  const auto length = from_integer(result_value.size(), result.length().type());
  const array_typet type(result.type().subtype(), length);
  return make_string(result_value, type);
}

/// Construct a string_builtin_functiont object from a function application
/// \return a unique pointer to the created object, this unique pointer is empty
///   if the function does not correspond to one of the supported
///   builtin_functions.
static std::unique_ptr<string_builtin_functiont> to_string_builtin_function(
  const function_application_exprt &fun_app,
  array_poolt &array_pool)
{
  const auto name = expr_checked_cast<symbol_exprt>(fun_app.function());
  const irep_idt &id = is_ssa_expr(name) ? to_ssa_expr(name).get_object_name()
                                         : name.get_identifier();

  if(id == ID_cprover_string_insert_func)
    return std::unique_ptr<string_builtin_functiont>(
      new string_insertion_builtin_functiont(fun_app.arguments(), array_pool));

  if(id == ID_cprover_string_concat_func)
    return util_make_unique<string_concatenation_builtin_functiont>(
      fun_app.arguments(), array_pool);

  if(id == ID_cprover_string_concat_char_func)
    return util_make_unique<string_concat_char_builtin_functiont>(
      fun_app.arguments(), array_pool);

  return {};
}

string_dependenciest::string_nodet &
string_dependenciest::get_node(const array_string_exprt &e)
{
  auto entry_inserted = node_index_pool.emplace(e, string_nodes.size());
  if(!entry_inserted.second)
    return string_nodes[entry_inserted.first->second];

  string_nodes.emplace_back(e, entry_inserted.first->second);
  return string_nodes.back();
}

std::unique_ptr<const string_dependenciest::string_nodet>
string_dependenciest::node_at(const array_string_exprt &e) const
{
  const auto &it = node_index_pool.find(e);
  if(it != node_index_pool.end())
    return util_make_unique<const string_nodet>(string_nodes.at(it->second));
  return {};
}

string_dependenciest::builtin_function_nodet string_dependenciest::make_node(
  std::unique_ptr<string_builtin_functiont> &builtin_function)
{
  const builtin_function_nodet builtin_function_node(
    builtin_function_nodes.size());
  builtin_function_nodes.emplace_back();
  builtin_function_nodes.back().swap(builtin_function);
  return builtin_function_node;
}

const string_builtin_functiont &string_dependenciest::get_builtin_function(
  const builtin_function_nodet &node) const
{
  PRECONDITION(node.index < builtin_function_nodes.size());
  return *(builtin_function_nodes[node.index]);
}

const std::vector<string_dependenciest::builtin_function_nodet> &
string_dependenciest::dependencies(
  const string_dependenciest::string_nodet &node) const
{
  return node.dependencies;
}

void string_dependenciest::add_dependency(
  const array_string_exprt &e,
  const builtin_function_nodet &builtin_function_node)
{
  if(e.id() == ID_if)
  {
    const auto if_expr = to_if_expr(e);
    const auto &true_case = to_array_string_expr(if_expr.true_case());
    const auto &false_case = to_array_string_expr(if_expr.false_case());
    add_dependency(true_case, builtin_function_node);
    add_dependency(false_case, builtin_function_node);
    return;
  }
  string_nodet &string_node = get_node(e);
  string_node.dependencies.push_back(builtin_function_node);
}

void string_dependenciest::add_unknown_dependency(const array_string_exprt &e)
{
  if(e.id() == ID_if)
  {
    const auto if_expr = to_if_expr(e);
    const auto &true_case = to_array_string_expr(if_expr.true_case());
    const auto &false_case = to_array_string_expr(if_expr.false_case());
    add_unknown_dependency(true_case);
    add_unknown_dependency(false_case);
    return;
  }
  string_nodet &string_node = get_node(e);
  string_node.depends_on_unknown_builtin_function = true;
}

static void add_unknown_dependency_to_string_subexprs(
  string_dependenciest &dependencies,
  const function_application_exprt &fun_app,
  array_poolt &array_pool)
{
  for(const auto &expr : fun_app.arguments())
  {
    std::for_each(
      expr.depth_begin(), expr.depth_end(), [&](const exprt &e) { // NOLINT
        if(is_refined_string_type(e.type()))
        {
          const auto &string_struct = expr_checked_cast<struct_exprt>(e);
          const array_string_exprt string =
            array_pool.find(string_struct.op1(), string_struct.op0());
          dependencies.add_unknown_dependency(string);
        }
      });
  }
}

static void add_dependency_to_string_subexprs(
  string_dependenciest &dependencies,
  const function_application_exprt &fun_app,
  const string_dependenciest::builtin_function_nodet &builtin_function_node,
  array_poolt &array_pool)
{
  PRECONDITION(fun_app.arguments()[0].type().id() != ID_pointer);
  if(
    fun_app.arguments().size() > 1 &&
    fun_app.arguments()[1].type().id() == ID_pointer)
  {
    // Case where the result is given as a pointer argument
    const array_string_exprt string =
      array_pool.find(fun_app.arguments()[1], fun_app.arguments()[0]);
    dependencies.add_dependency(string, builtin_function_node);
  }

  for(const auto &expr : fun_app.arguments())
  {
    std::for_each(
      expr.depth_begin(),
      expr.depth_end(),
      [&](const exprt &e) { // NOLINT
        if(is_refined_string_type(e.type()))
        {
          const auto string_struct = expr_checked_cast<struct_exprt>(e);
          const auto string = array_pool.of_argument(string_struct);
          dependencies.add_dependency(string, builtin_function_node);
        }
      });
  }
}

optionalt<exprt> string_dependenciest::eval(
  const array_string_exprt &s,
  const std::function<exprt(const exprt &)> &get_value) const
{
  const auto &it = node_index_pool.find(s);
  if(it == node_index_pool.end())
    return {};

  if(eval_string_cache[it->second])
    return eval_string_cache[it->second];

  const auto node = string_nodes[it->second];
  const auto &f = node.result_from;
  if(
    f && node.dependencies.size() == 1 &&
    !node.depends_on_unknown_builtin_function)
  {
    const auto value_opt = get_builtin_function(*f).eval(get_value);
    eval_string_cache[it->second] = value_opt;
    return value_opt;
  }
  return {};
}

void string_dependenciest::clean_cache()
{
  eval_string_cache.resize(string_nodes.size());
  for(auto &e : eval_string_cache)
    e.reset();
}

bool add_node(
  string_dependenciest &dependencies,
  const equal_exprt &equation,
  array_poolt &array_pool)
{
  const auto fun_app =
    expr_try_dynamic_cast<function_application_exprt>(equation.rhs());
  if(!fun_app)
    return false;

  auto builtin_function = to_string_builtin_function(*fun_app, array_pool);

  if(!builtin_function)
  {
    add_unknown_dependency_to_string_subexprs(
      dependencies, *fun_app, array_pool);
    return true;
  }

  const auto &builtin_function_node = dependencies.make_node(builtin_function);
  // Warning: `builtin_function` has been emptied and should not be used anymore

  if(
    const auto &string_result =
      dependencies.get_builtin_function(builtin_function_node).string_result())
  {
    dependencies.add_dependency(*string_result, builtin_function_node);
    auto &node = dependencies.get_node(*string_result);
    node.result_from = builtin_function_node;
  }
  else
    add_dependency_to_string_subexprs(
      dependencies, *fun_app, builtin_function_node, array_pool);

  return true;
}

void string_dependenciest::for_each_successor(
  const nodet &node,
  const std::function<void(const nodet &)> &f) const
{
  if(node.kind == nodet::BUILTIN)
  {
    const auto &builtin = builtin_function_nodes[node.index];
    for(const auto &s : builtin->string_arguments())
    {
      if(const auto node = node_at(s))
        f(nodet(*node));
    }
  }
  else if(node.kind == nodet::STRING)
  {
    const auto &s_node = string_nodes[node.index];
    std::for_each(
      s_node.dependencies.begin(),
      s_node.dependencies.end(),
      [&](const builtin_function_nodet &p) { f(nodet(p)); });
  }
  else
    UNREACHABLE;
}

void string_dependenciest::for_each_node(
  const std::function<void(const nodet &)> &f) const
{
  for(const auto string_node : string_nodes)
    f(nodet(string_node));
  for(std::size_t i = 0; i < builtin_function_nodes.size(); ++i)
    f(nodet(builtin_function_nodet(i)));
}

void string_dependenciest::output_dot(std::ostream &stream) const
{
  const auto for_each =
    [&](const std::function<void(const nodet &)> &f) { // NOLINT
      for_each_node(f);
    };
  const auto for_each_succ =
    [&](const nodet &n, const std::function<void(const nodet &)> &f) { // NOLINT
      for_each_successor(n, f);
    };
  const auto node_to_string = [&](const nodet &n) { // NOLINT
    std::stringstream ostream;
    if(n.kind == nodet::BUILTIN)
      ostream << "builtin_" << n.index;
    else
      ostream << '"' << format(string_nodes[n.index].expr) << '"';
    return ostream.str();
  };
  stream << "digraph dependencies {\n";
  output_dot_generic<nodet>(stream, for_each, for_each_succ, node_to_string);
  stream << '}' << std::endl;
}
