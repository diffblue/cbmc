/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_object_statistics.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <util/expr_util.h>
#include <util/simplify_expr.h>

#include <algorithm>
#include <map>
#include <ostream>
#include <stack>

#ifdef DEBUG
#  include <iostream>
#endif

exprt assume_eq(abstract_environmentt &env, exprt expr, const namespacet &ns);
exprt assume_noteq(
  abstract_environmentt &env,
  exprt expr,
  const namespacet &ns);
exprt assume_le(abstract_environmentt &env, exprt expr, const namespacet &ns);

abstract_value_pointert as_value(const abstract_object_pointert &obj);
bool is_value(const abstract_object_pointert &obj);

std::vector<abstract_object_pointert> eval_operands(
  const exprt &expr,
  const abstract_environmentt &env,
  const namespacet &ns);

abstract_object_pointert
abstract_environmentt::eval(const exprt &expr, const namespacet &ns) const
{
  if(bottom)
    return abstract_object_factory(expr.type(), ns, false, true);

  // first try to canonicalise, including constant folding
  const exprt &simplified_expr = simplify_expr(expr, ns);

  const irep_idt simplified_id = simplified_expr.id();
  if(simplified_id == ID_symbol)
    return resolve_symbol(simplified_expr, ns);

  if(
    simplified_id == ID_member || simplified_id == ID_index ||
    simplified_id == ID_dereference)
  {
    auto access_expr = simplified_expr;
    auto target = eval(access_expr.operands()[0], ns);

    return target->expression_transform(
      access_expr, eval_operands(access_expr, *this, ns), *this, ns);
  }

  if(
    simplified_id == ID_array || simplified_id == ID_struct ||
    simplified_id == ID_constant || simplified_id == ID_address_of)
  {
    return abstract_object_factory(simplified_expr.type(), simplified_expr, ns);
  }

  // No special handling required by the abstract environment
  // delegate to the abstract object
  if(!simplified_expr.operands().empty())
  {
    return eval_expression(simplified_expr, ns);
  }
  else
  {
    // It is important that this is top as the abstract object may not know
    // how to handle the expression
    return abstract_object_factory(simplified_expr.type(), ns, true, false);
  }
}

abstract_object_pointert abstract_environmentt::resolve_symbol(
  const exprt &expr,
  const namespacet &ns) const
{
  const symbol_exprt &symbol(to_symbol_expr(expr));
  const auto symbol_entry = map.find(symbol.get_identifier());

  if(symbol_entry.has_value())
    return symbol_entry.value();
  return abstract_object_factory(expr.type(), ns, true, false);
}

bool abstract_environmentt::assign(
  const exprt &expr,
  const abstract_object_pointert &value,
  const namespacet &ns)
{
  PRECONDITION(value);

  if(value->is_bottom())
  {
    bool bottom_at_start = this->is_bottom();
    this->make_bottom();
    return !bottom_at_start;
  }

  abstract_object_pointert lhs_value = nullptr;
  // Build a stack of index, member and dereference accesses which
  // we will work through the relevant abstract objects
  exprt s = expr;
  std::stack<exprt> stactions; // I'm not a continuation, honest guv'
  while(s.id() != ID_symbol)
  {
    if(s.id() == ID_index || s.id() == ID_member || s.id() == ID_dereference)
    {
      stactions.push(s);
      s = s.operands()[0];
    }
    else
    {
      lhs_value = eval(s, ns);
      break;
    }
  }

  if(!lhs_value)
  {
    INVARIANT(s.id() == ID_symbol, "Have a symbol or a stack");
    lhs_value = resolve_symbol(s, ns);
  }

  abstract_object_pointert final_value;

  // This is the root abstract object that is in the map of abstract objects
  // It might not have the same type as value if the above stack isn't empty

  if(!stactions.empty())
  {
    // The symbol is not in the map - it is therefore top
    final_value = write(lhs_value, value, stactions, ns, false);
  }
  else
  {
    // If we don't have a symbol on the LHS, then we must have some expression
    // that we can write to (i.e. a pointer, an array, a struct) This appears
    // to be none of that.
    if(s.id() != ID_symbol)
    {
      throw std::runtime_error("invalid l-value");
    }
    // We can assign the AO directly to the symbol
    final_value = value;
  }

  const typet &lhs_type = ns.follow(lhs_value->type());
  const typet &rhs_type = ns.follow(final_value->type());

  // Write the value for the root symbol back into the map
  INVARIANT(
    lhs_type == rhs_type,
    "Assignment types must match"
    "\n"
    "lhs_type :" +
      lhs_type.pretty() +
      "\n"
      "rhs_type :" +
      rhs_type.pretty());

  // If LHS was directly the symbol
  if(s.id() == ID_symbol)
  {
    symbol_exprt symbol_expr = to_symbol_expr(s);

    if(final_value != lhs_value)
    {
      CHECK_RETURN(!symbol_expr.get_identifier().empty());
      map.insert_or_replace(symbol_expr.get_identifier(), final_value);
    }
  }
  return true;
}

abstract_object_pointert abstract_environmentt::write(
  const abstract_object_pointert &lhs,
  const abstract_object_pointert &rhs,
  std::stack<exprt> remaining_stack,
  const namespacet &ns,
  bool merge_write)
{
  PRECONDITION(!remaining_stack.empty());
  const exprt &next_expr = remaining_stack.top();
  remaining_stack.pop();

  const irep_idt &stack_head_id = next_expr.id();
  INVARIANT(
    stack_head_id == ID_index || stack_head_id == ID_member ||
      stack_head_id == ID_dereference,
    "Write stack expressions must be index, member, or dereference");

  return lhs->write(*this, ns, remaining_stack, next_expr, rhs, merge_write);
}

bool abstract_environmentt::assume(const exprt &expr, const namespacet &ns)
{
  // We should only attempt to assume Boolean things
  // This should be enforced by the well-structured-ness of the
  // goto-program and the way assume is used.
  PRECONDITION(expr.type().id() == ID_bool);

  exprt assumption = do_assume(expr, ns);

  if(assumption.id() != ID_nil) // I.E. actually a value
  {
    // Should be of the right type
    INVARIANT(
      assumption.type().id() == ID_bool, "simplification preserves type");

    if(assumption.is_false())
    {
      bool currently_bottom = is_bottom();
      make_bottom();
      return !currently_bottom;
    }
  }

  return false;
}

exprt abstract_environmentt::do_assume(exprt expr, const namespacet &ns)
{
  auto expr_id = expr.id();

  if(expr_id == ID_not)
  {
    auto not_expr = to_not_expr(expr);
    auto result = do_assume(not_expr.op(), ns);
    if(result.is_boolean())
      result = result.is_true() ? exprt(false_exprt()) : true_exprt();
    return result;
  }

  if(expr_id == ID_equal)
    return assume_eq(*this, expr, ns);
  if(expr_id == ID_notequal)
    return assume_noteq(*this, expr, ns);
  if(expr_id == ID_le)
    return assume_le(*this, expr, ns);

  auto result = eval(expr, ns)->to_constant();
  return result;
}

abstract_object_pointert abstract_environmentt::abstract_object_factory(
  const typet &type,
  const namespacet &ns,
  bool top,
  bool bttm) const
{
  exprt empty_constant_expr = nil_exprt();
  return abstract_object_factory(
    type, top, bttm, empty_constant_expr, *this, ns);
}

abstract_object_pointert abstract_environmentt::abstract_object_factory(
  const typet &type,
  const exprt &e,
  const namespacet &ns) const
{
  return abstract_object_factory(type, false, false, e, *this, ns);
}

abstract_object_pointert abstract_environmentt::abstract_object_factory(
  const typet &type,
  bool top,
  bool bttm,
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  return object_factory->get_abstract_object(
    type, top, bttm, e, environment, ns);
}

abstract_object_pointert abstract_environmentt::add_object_context(
  const abstract_object_pointert &abstract_object) const
{
  return object_factory->wrap_with_context(abstract_object);
}

bool abstract_environmentt::merge(const abstract_environmentt &env)
{
  // for each entry in the incoming environment we need to either add it
  // if it is new, or merge with the existing key if it is not present

  if(bottom)
  {
    *this = env;
    return !env.bottom;
  }
  else if(env.bottom)
  {
    return false;
  }
  else
  {
    // For each element in the intersection of map and env.map merge
    // If the result of the merge is top, remove from the map
    bool modified = false;
    decltype(env.map)::delta_viewt delta_view;
    env.map.get_delta_view(map, delta_view);
    for(const auto &entry : delta_view)
    {
      bool object_modified = false;
      abstract_object_pointert new_object = abstract_objectt::merge(
        entry.get_other_map_value(), entry.m, object_modified);
      modified |= object_modified;
      map.replace(entry.k, new_object);
    }

    return modified;
  }
}

void abstract_environmentt::havoc(const std::string &havoc_string)
{
  // TODO(tkiley): error reporting
  make_top();
}

void abstract_environmentt::make_top()
{
  // since we assume anything is not in the map is top this is sufficient
  map.clear();
  bottom = false;
}

void abstract_environmentt::make_bottom()
{
  map.clear();
  bottom = true;
}

bool abstract_environmentt::is_bottom() const
{
  return map.empty() && bottom;
}

bool abstract_environmentt::is_top() const
{
  return map.empty() && !bottom;
}

void abstract_environmentt::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  out << "{\n";

  decltype(map)::viewt view;
  map.get_view(view);
  for(const auto &entry : view)
  {
    out << entry.first << " () -> ";
    entry.second->output(out, ai, ns);
    out << "\n";
  }
  out << "}\n";
}

bool abstract_environmentt::verify() const
{
  decltype(map)::viewt view;
  map.get_view(view);
  for(const auto &entry : view)
  {
    if(entry.second == nullptr)
    {
      return false;
    }
  }
  return true;
}

abstract_object_pointert abstract_environmentt::eval_expression(
  const exprt &e,
  const namespacet &ns) const
{
  // We create a temporary top abstract object (according to the
  // type of the expression), and call expression transform on it.
  // The value of the temporary abstract object is ignored, its
  // purpose is just to dispatch the expression transform call to
  // a concrete subtype of abstract_objectt.
  auto eval_obj = abstract_object_factory(e.type(), ns, true, false);
  auto operands = eval_operands(e, *this, ns);

  return eval_obj->expression_transform(e, operands, *this, ns);
}

void abstract_environmentt::erase(const symbol_exprt &expr)
{
  map.erase_if_exists(expr.get_identifier());
}

std::vector<abstract_environmentt::map_keyt>
abstract_environmentt::modified_symbols(
  const abstract_environmentt &first,
  const abstract_environmentt &second)
{
  // Find all symbols who have different write locations in each map
  std::vector<abstract_environmentt::map_keyt> symbols_diff;
  decltype(first.map)::viewt view;
  first.map.get_view(view);
  for(const auto &entry : view)
  {
    const auto &second_entry = second.map.find(entry.first);
    if(second_entry.has_value())
    {
      if(second_entry.value().get()->has_been_modified(entry.second))
      {
        CHECK_RETURN(!entry.first.empty());
        symbols_diff.push_back(entry.first);
      }
    }
  }

  // Add any symbols that are only in the second map
  for(const auto &entry : second.map.get_view())
  {
    const auto &second_entry = first.map.find(entry.first);
    if(!second_entry.has_value())
    {
      CHECK_RETURN(!entry.first.empty());
      symbols_diff.push_back(entry.first);
    }
  }
  return symbols_diff;
}

static std::size_t count_globals(const namespacet &ns)
{
  auto const &symtab = ns.get_symbol_table();
  auto val = std::count_if(
    symtab.begin(),
    symtab.end(),
    [](const symbol_tablet::const_iteratort::value_type &sym) {
      return sym.second.is_lvalue && sym.second.is_static_lifetime;
    });
  return val;
}

abstract_object_statisticst
abstract_environmentt::gather_statistics(const namespacet &ns) const
{
  abstract_object_statisticst statistics = {};
  statistics.number_of_globals = count_globals(ns);
  decltype(map)::viewt view;
  map.get_view(view);
  abstract_object_visitedt visited;
  for(auto const &object : view)
  {
    if(visited.find(object.second) == visited.end())
    {
      object.second->get_statistics(statistics, visited, *this, ns);
    }
  }
  return statistics;
}

std::vector<abstract_object_pointert> eval_operands(
  const exprt &expr,
  const abstract_environmentt &env,
  const namespacet &ns)
{
  std::vector<abstract_object_pointert> operands;

  for(const auto &op : expr.operands())
    operands.push_back(env.eval(op, ns));

  return operands;
}

///////////
abstract_value_pointert as_value(const abstract_object_pointert &obj)
{
  auto context_value =
    std::dynamic_pointer_cast<const context_abstract_objectt>(obj);

  return context_value
           ? as_value(context_value->unwrap_context())
           : std::dynamic_pointer_cast<const abstract_value_objectt>(obj);
}

bool is_value(const abstract_object_pointert &obj)
{
  return as_value(obj) != nullptr;
}

exprt assume_eq(abstract_environmentt &env, exprt expr, const namespacet &ns)
{
  auto equal_expr = to_binary_expr(expr);

  auto left = env.eval(equal_expr.lhs(), ns);
  auto right = env.eval(equal_expr.rhs(), ns);

  if(left->is_top() || right->is_top())
    return nil_exprt();
  if(!is_value(left) || !is_value(right))
    return nil_exprt();

  auto meet = left->meet(right);

  if(meet->is_bottom())
    return false_exprt();

  if(is_lvalue(equal_expr.lhs()))
    env.assign(equal_expr.lhs(), meet, ns);
  if(is_lvalue(equal_expr.rhs()))
    env.assign(equal_expr.rhs(), meet, ns);
  return true_exprt();
}

exprt assume_noteq(abstract_environmentt &env, exprt expr, const namespacet &ns)
{
  auto notequal_expr = to_binary_expr(expr);

  auto left = env.eval(notequal_expr.lhs(), ns);
  auto right = env.eval(notequal_expr.rhs(), ns);

  if(left->is_top() || right->is_top())
    return nil_exprt();
  if(!is_value(left) || !is_value(right))
    return nil_exprt();

  auto meet = left->meet(right);

  if(meet->is_bottom())
    return true_exprt();

  return false_exprt();
}

exprt assume_le(abstract_environmentt &env, exprt expr, const namespacet &ns)
{
  auto lessthan_or_equal_expr = to_binary_expr(expr);

  auto left = env.eval(lessthan_or_equal_expr.lhs(), ns);
  auto right = env.eval(lessthan_or_equal_expr.rhs(), ns);

  if(left->is_top() || right->is_top())
    return nil_exprt();
  auto left_value = as_value(left);
  auto right_value = as_value(right);

  if(left_value == nullptr || right_value == nullptr)
    return nil_exprt();

  auto left_lower = left_value->to_interval().get_lower();
  auto right_upper = right_value->to_interval().get_upper();

  auto reduced_le_expr = binary_relation_exprt(left_lower, ID_le, right_upper);
  return env.eval(reduced_le_expr, ns)->to_constant();
}