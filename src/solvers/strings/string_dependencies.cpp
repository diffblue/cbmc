/*******************************************************************\

Module: String solver

Author: Diffblue Ltd.

\*******************************************************************/

#include "string_dependencies.h"
#include "string_concatenation_builtin_function.h"
#include "string_format_builtin_function.h"
#include <unordered_set>
#include <util/expr_iterator.h>
#include <util/graph.h>
#include <util/make_unique.h>
#include <util/ssa_expr.h>

/// Applies `f` on all strings contained in `e` that are not if-expressions.
/// For instance on input `cond1?s1:cond2?s2:s3` we apply `f` on s1, s2 and s3.
static void for_each_atomic_string(
  const array_string_exprt &e,
  const std::function<void(const array_string_exprt &)> f);

/// Construct a string_builtin_functiont object from a function application
/// \return a unique pointer to the created object
static std::unique_ptr<string_builtin_functiont> to_string_builtin_function(
  const function_application_exprt &fun_app,
  const exprt &return_code,
  array_poolt &array_pool)
{
  const auto name = expr_checked_cast<symbol_exprt>(fun_app.function());
  PRECONDITION(!is_ssa_expr(name));

  const irep_idt &id = name.get_identifier();

  if(id == ID_cprover_string_insert_func)
    return util_make_unique<string_insertion_builtin_functiont>(
      return_code, fun_app.arguments(), array_pool);

  if(id == ID_cprover_string_concat_func)
    return util_make_unique<string_concatenation_builtin_functiont>(
      return_code, fun_app.arguments(), array_pool);

  if(id == ID_cprover_string_concat_char_func)
    return util_make_unique<string_concat_char_builtin_functiont>(
      return_code, fun_app.arguments(), array_pool);

  if(id == ID_cprover_string_format_func)
    return util_make_unique<string_format_builtin_functiont>(
      return_code, fun_app.arguments(), array_pool);

  if(id == ID_cprover_string_of_int_func)
    return util_make_unique<string_of_int_builtin_functiont>(
      return_code, fun_app.arguments(), array_pool);

  if(id == ID_cprover_string_char_set_func)
    return util_make_unique<string_set_char_builtin_functiont>(
      return_code, fun_app.arguments(), array_pool);

  if(id == ID_cprover_string_to_lower_case_func)
    return util_make_unique<string_to_lower_case_builtin_functiont>(
      return_code, fun_app.arguments(), array_pool);

  if(id == ID_cprover_string_to_upper_case_func)
    return util_make_unique<string_to_upper_case_builtin_functiont>(
      return_code, fun_app.arguments(), array_pool);

  return util_make_unique<string_builtin_function_with_no_evalt>(
    return_code, fun_app, array_pool);
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

string_dependenciest::builtin_function_nodet &string_dependenciest::make_node(
  std::unique_ptr<string_builtin_functiont> builtin_function)
{
  builtin_function_nodes.emplace_back(
    std::move(builtin_function), builtin_function_nodes.size());
  return builtin_function_nodes.back();
}

const string_builtin_functiont &string_dependenciest::get_builtin_function(
  const builtin_function_nodet &node) const
{
  return *node.data;
}

static void for_each_atomic_string(
  const array_string_exprt &e,
  const std::function<void(const array_string_exprt &)> f)
{
  if(e.id() != ID_if)
    return f(e);

  const auto if_expr = to_if_expr(e);
  for_each_atomic_string(to_array_string_expr(if_expr.true_case()), f);
  for_each_atomic_string(to_array_string_expr(if_expr.false_case()), f);
}

void string_dependenciest::add_dependency(
  const array_string_exprt &e,
  const builtin_function_nodet &builtin_function_node)
{
  for_each_atomic_string(e, [&](const array_string_exprt &s) { //NOLINT
    string_nodet &string_node = get_node(s);
    string_node.dependencies.push_back(builtin_function_node.index);
  });
}

void string_dependenciest::clear()
{
  builtin_function_nodes.clear();
  string_nodes.clear();
  node_index_pool.clear();
  clean_cache();
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
          const auto string = of_argument(array_pool, string_struct);
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
  if(f && node.dependencies.size() == 1)
  {
    const auto value_opt = builtin_function_nodes[*f].data->eval(get_value);
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

optionalt<exprt> add_node(
  string_dependenciest &dependencies,
  const exprt &expr,
  array_poolt &array_pool,
  symbol_generatort &fresh_symbol)
{
  const auto fun_app = expr_try_dynamic_cast<function_application_exprt>(expr);
  if(!fun_app)
  {
    exprt copy = expr;
    bool copy_differs_from_expr = false;
    for(std::size_t i = 0; i < expr.operands().size(); ++i)
    {
      auto new_op =
        add_node(dependencies, expr.operands()[i], array_pool, fresh_symbol);
      if(new_op)
      {
        copy.operands()[i] = *new_op;
        copy_differs_from_expr = true;
      }
    }
    if(copy_differs_from_expr)
      return copy;
    return {};
  }

  const exprt return_code = fresh_symbol("string_builtin_return", expr.type());
  auto builtin_function =
    to_string_builtin_function(*fun_app, return_code, array_pool);

  CHECK_RETURN(builtin_function != nullptr);
  const auto &builtin_function_node =
    dependencies.make_node(std::move(builtin_function));

  if(
    const auto &string_result =
      dependencies.get_builtin_function(builtin_function_node).string_result())
  {
    dependencies.add_dependency(*string_result, builtin_function_node);
    auto &node = dependencies.get_node(*string_result);
    node.result_from = builtin_function_node.index;

    // Ensure all atomic strings in the argument have an associated node
    for(const auto arg : builtin_function_node.data->string_arguments())
    {
      for_each_atomic_string(
        arg, [&](const array_string_exprt &atomic) { // NOLINT
          (void)dependencies.get_node(atomic);
        });
    }
  }
  else
    add_dependency_to_string_subexprs(
      dependencies, *fun_app, builtin_function_node, array_pool);

  return return_code;
}

void string_dependenciest::for_each_dependency(
  const builtin_function_nodet &node,
  const std::function<void(const string_nodet &)> &f) const
{
  for(const auto &s : node.data->string_arguments())
  {
    std::vector<std::reference_wrapper<const exprt>> stack({s});
    while(!stack.empty())
    {
      const auto current = stack.back();
      stack.pop_back();
      if(const auto if_expr = expr_try_dynamic_cast<if_exprt>(current.get()))
      {
        stack.emplace_back(if_expr->true_case());
        stack.emplace_back(if_expr->false_case());
      }
      else
      {
        const auto string_node = node_at(to_array_string_expr(current));
        INVARIANT(
          string_node,
          "dependencies of the node should have been added to the graph at "
          "node creation " +
            current.get().pretty());
        f(*string_node);
      }
    }
  }
}

void string_dependenciest::for_each_dependency(
  const string_nodet &node,
  const std::function<void(const builtin_function_nodet &)> &f) const
{
  for(const std::size_t &index : node.dependencies)
    f(builtin_function_nodes[index]);
}

void string_dependenciest::for_each_successor(
  const nodet &node,
  const std::function<void(const nodet &)> &f) const
{
  switch(node.kind)
  {
  case nodet::BUILTIN:
    for_each_dependency(
      builtin_function_nodes[node.index],
      [&](const string_nodet &n) { return f(nodet(n)); });
    break;

  case nodet::STRING:
    for_each_dependency(
      string_nodes[node.index],
      [&](const builtin_function_nodet &n) { return f(nodet(n)); });
    break;
  }
}

void string_dependenciest::for_each_node(
  const std::function<void(const nodet &)> &f) const
{
  for(const auto string_node : string_nodes)
    f(nodet(string_node));
  for(std::size_t i = 0; i < builtin_function_nodes.size(); ++i)
    f(nodet(builtin_function_nodes[i]));
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
      ostream << '"' << builtin_function_nodes[n.index].data->name() << '_'
              << n.index << '"';
    else
      ostream << '"' << format(string_nodes[n.index].expr) << '"';
    return ostream.str();
  };
  stream << "digraph dependencies {\n";
  output_dot_generic<nodet>(
    stream, for_each, for_each_succ, node_to_string, node_to_string);
  stream << '}' << std::endl;
}

string_constraintst
string_dependenciest::add_constraints(string_constraint_generatort &generator)
{
  std::unordered_set<nodet, node_hash> test_dependencies;
  for(const auto &builtin : builtin_function_nodes)
  {
    if(builtin.data->maybe_testing_function())
      test_dependencies.insert(nodet(builtin));
  }

  get_reachable(
    test_dependencies,
    [&](
      const nodet &n,
      const std::function<void(const nodet &)> &f) { // NOLINT
      for_each_successor(n, f);
    });

  string_constraintst constraints;
  for(const auto &node : builtin_function_nodes)
  {
    if(test_dependencies.count(nodet(node)))
    {
      const auto &builtin = builtin_function_nodes[node.index];
      merge(constraints, builtin.data->constraints(generator));
    }
    else
      constraints.existential.push_back(node.data->length_constraint());
  }
  return constraints;
}
