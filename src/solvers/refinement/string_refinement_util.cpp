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
#include "string_refinement_util.h"

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

string_insertion_builtin_functiont::string_insertion_builtin_functiont(
  const std::vector<exprt> &fun_args,
  array_poolt &array_pool)
{
  PRECONDITION(fun_args.size() > 3);
  const auto arg1 = expr_checked_cast<struct_exprt>(fun_args[2]);
  input1 = array_pool.find(arg1.op1(), arg1.op0());
  const auto arg2 = expr_checked_cast<struct_exprt>(fun_args[3]);
  input2 = array_pool.find(arg2.op1(), arg2.op0());
  result = array_pool.find(fun_args[1], fun_args[0]);
  args.insert(args.end(), fun_args.begin() + 4, fun_args.end());
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
    return std::unique_ptr<string_builtin_functiont>(
      new string_insertion_builtin_functiont(fun_app.arguments(), array_pool));

  return {};
}

string_dependencest::string_nodet &
string_dependencest::get_node(const array_string_exprt &e)
{
  auto entry_inserted = node_index_pool.emplace(e, string_nodes.size());
  if(!entry_inserted.second)
    return string_nodes[entry_inserted.first->second];

  string_nodes.emplace_back();
  return string_nodes.back();
}

string_dependencest::builtin_function_nodet string_dependencest::make_node(
  std::unique_ptr<string_builtin_functiont> &builtin_function)
{
  const builtin_function_nodet builtin_function_node(
    builtin_function_nodes.size());
  builtin_function_nodes.emplace_back();
  builtin_function_nodes.back().swap(builtin_function);
  return builtin_function_node;
}

const string_builtin_functiont &string_dependencest::get_builtin_function(
  const builtin_function_nodet &node) const
{
  PRECONDITION(node.index < builtin_function_nodes.size());
  return *(builtin_function_nodes[node.index]);
}

const std::vector<string_dependencest::builtin_function_nodet> &
string_dependencest::dependencies(
  const string_dependencest::string_nodet &node) const
{
  return node.dependencies;
}

void string_dependencest::add_dependency(
  const array_string_exprt &e,
  const builtin_function_nodet &builtin_function_node)
{
  string_nodet &string_node = get_node(e);
  string_node.dependencies.push_back(builtin_function_node);
}

void string_dependencest::add_unknown_dependency(const array_string_exprt &e)
{
  string_nodet &string_node = get_node(e);
  string_node.depends_on_unknown_builtin_function = true;
}

static void add_unknown_dependency_to_string_subexprs(
  string_dependencest &dependencies,
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
  string_dependencest &dependencies,
  const function_application_exprt &fun_app,
  const string_dependencest::builtin_function_nodet &builtin_function_node,
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

string_dependencest::node_indext string_dependencest::size() const
{
  return builtin_function_nodes.size() + string_nodes.size();
}

/// Convert an index of a string node in `string_nodes` to the node_indext for
/// the same node
static std::size_t string_index_to_node_index(const std::size_t string_index)
{
  return 2 * string_index + 1;
}

/// Convert an index of a builtin function node to the node_indext for
/// the same node
static std::size_t
builtin_function_index_to_node_index(const std::size_t builtin_index)
{
  return 2 * builtin_index;
}

string_dependencest::node_indext
string_dependencest::node_index(const builtin_function_nodet &n) const
{
  return builtin_function_index_to_node_index(n.index);
}

string_dependencest::node_indext
string_dependencest::node_index(const array_string_exprt &s) const
{
  return string_index_to_node_index(node_index_pool.at(s));
}

optionalt<string_dependencest::builtin_function_nodet>
string_dependencest::get_builtin_function_node(node_indext i) const
{
  if(i % 2 == 0)
    return builtin_function_nodet(i / 2);
  return {};
}

optionalt<string_dependencest::string_nodet>
string_dependencest::get_string_node(node_indext i) const
{
  if(i % 2 == 1 && i / 2 < string_nodes.size())
    return string_nodes[i / 2];
  return {};
}

bool add_node(
  string_dependencest &dependencies,
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
    dependencies.add_dependency(*string_result, builtin_function_node);
  else
    add_dependency_to_string_subexprs(
      dependencies, *fun_app, builtin_function_node, array_pool);

  return true;
}

void string_dependencest::for_each_successor(
  const std::size_t &i,
  const std::function<void(const std::size_t &)> &f) const
{
  if(const auto &builtin_function_node = get_builtin_function_node(i))
  {
    const string_builtin_functiont &p =
      get_builtin_function(*builtin_function_node);
    std::for_each(
      p.string_arguments().begin(),
      p.string_arguments().end(),
      [&](const array_string_exprt &s) { f(node_index(s)); });
  }
  else if(const auto &s = get_string_node(i))
  {
    std::for_each(
      s->dependencies.begin(),
      s->dependencies.end(),
      [&](const builtin_function_nodet &p) { f(node_index(p)); });
  }
  else
    UNREACHABLE;
}

void string_dependencest::output_dot(std::ostream &stream) const
{
  const auto for_each_node =
    [&](const std::function<void(const std::size_t &)> &f) { // NOLINT
      for(std::size_t i = 0; i < string_nodes.size(); ++i)
        f(string_index_to_node_index(i));
      for(std::size_t i = 0; i < builtin_function_nodes.size(); ++i)
        f(builtin_function_index_to_node_index(i));
    };

  const auto for_each_succ = [&](
    const std::size_t &i,
    const std::function<void(const std::size_t &)> &f) { // NOLINT
    for_each_successor(i, f);
  };

  const auto node_to_string = [&](const std::size_t &i) { // NOLINT
    return std::to_string(i);
  };
  stream << "digraph dependencies {\n";
  output_dot_generic<std::size_t>(
    stream, for_each_node, for_each_succ, node_to_string);
  stream << '}' << std::endl;
}
