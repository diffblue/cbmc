/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_object_statistics.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>

#include <util/expr_util.h>
#include <util/simplify_expr.h>
#include <util/simplify_expr_class.h>
#include <util/simplify_utils.h>
#include <util/symbol_table.h>

#include <algorithm>
#include <map>
#include <ostream>
#include <stack>

#ifdef DEBUG
#  include <iostream>
#endif

typedef exprt (
  *assume_function)(abstract_environmentt &, const exprt &, const namespacet &);

static exprt
assume_not(abstract_environmentt &env, const exprt &expr, const namespacet &ns);
static exprt
assume_or(abstract_environmentt &env, const exprt &expr, const namespacet &ns);
static exprt
assume_and(abstract_environmentt &env, const exprt &expr, const namespacet &ns);
static exprt
assume_eq(abstract_environmentt &env, const exprt &expr, const namespacet &ns);
static exprt assume_noteq(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns);
static exprt assume_less_than(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns);
static exprt assume_greater_than(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns);

static abstract_value_pointert as_value(const abstract_object_pointert &obj);
static bool is_value(const abstract_object_pointert &obj);

std::vector<abstract_object_pointert> eval_operands(
  const exprt &expr,
  const abstract_environmentt &env,
  const namespacet &ns);

bool is_ptr_diff(const exprt &expr)
{
  return (expr.id() == ID_minus) &&
         (expr.operands()[0].type().id() == ID_pointer) &&
         (expr.operands()[1].type().id() == ID_pointer);
}

bool is_ptr_comparison(const exprt &expr)
{
  auto const &id = expr.id();
  bool is_comparison = id == ID_equal || id == ID_notequal || id == ID_lt ||
                       id == ID_le || id == ID_gt || id == ID_ge;

  return is_comparison && (expr.operands()[0].type().id() == ID_pointer) &&
         (expr.operands()[1].type().id() == ID_pointer);
}

static bool is_access_expr(const irep_idt &id)
{
  return id == ID_member || id == ID_index || id == ID_dereference;
}

static bool is_object_creation(const irep_idt &id)
{
  return id == ID_array || id == ID_struct || id == ID_constant ||
         id == ID_address_of;
}

static bool is_dynamic_allocation(const exprt &expr)
{
  return expr.id() == ID_side_effect && expr.get(ID_statement) == ID_allocate;
}

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
    is_access_expr(simplified_id) || is_ptr_diff(simplified_expr) ||
    is_ptr_comparison(simplified_expr))
  {
    auto const operands = eval_operands(simplified_expr, *this, ns);
    auto const &target = operands.front();

    return target->expression_transform(simplified_expr, operands, *this, ns);
  }

  if(is_object_creation(simplified_id))
    return abstract_object_factory(simplified_expr.type(), simplified_expr, ns);

  if(is_dynamic_allocation(simplified_expr))
    return abstract_object_factory(
      typet(ID_dynamic_object),
      exprt(ID_dynamic_object, simplified_expr.type()),
      ns);

  // No special handling required by the abstract environment
  // delegate to the abstract object
  if(!simplified_expr.operands().empty())
    return eval_expression(simplified_expr, ns);

  // It is important that this is top as the abstract object may not know
  // how to handle the expression
  return abstract_object_factory(simplified_expr.type(), ns, true, false);
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

  auto simplified = simplify_expr(expr, ns);
  auto assumption = do_assume(simplified, ns);

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

static auto assume_functions =
  std::map<irep_idt, assume_function>{{ID_not, assume_not},
                                      {ID_and, assume_and},
                                      {ID_or, assume_or},
                                      {ID_equal, assume_eq},
                                      {ID_notequal, assume_noteq},
                                      {ID_le, assume_less_than},
                                      {ID_lt, assume_less_than},
                                      {ID_ge, assume_greater_than},
                                      {ID_gt, assume_greater_than}};

// do_assume attempts to reduce the expression
// returns
//   true_exprt when the assumption does not hold
//   false_exprt if the assumption does not hold & the domain should go bottom
//   nil_exprt if the assumption can't be evaluated & we should give up
exprt abstract_environmentt::do_assume(const exprt &expr, const namespacet &ns)
{
  auto expr_id = expr.id();

  auto fn = assume_functions[expr_id];

  if(fn)
    return fn(*this, expr, ns);

  return eval(expr, ns)->to_constant();
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

const vsd_configt &abstract_environmentt::configuration() const
{
  return object_factory->config();
}

bool abstract_environmentt::merge(
  const abstract_environmentt &env,
  const goto_programt::const_targett &merge_location,
  widen_modet widen_mode)
{
  // for each entry in the incoming environment we need to either add it
  // if it is new, or merge with the existing key if it is not present
  if(bottom)
  {
    *this = env;
    return !env.bottom;
  }

  if(env.bottom)
    return false;

  // For each element in the intersection of map and env.map merge
  // If the result of the merge is top, remove from the map
  bool modified = false;
  for(const auto &entry : env.map.get_delta_view(map))
  {
    auto merge_result = abstract_objectt::merge(
      entry.get_other_map_value(), entry.m, merge_location, widen_mode);

    modified |= merge_result.modified;
    map.replace(entry.k, merge_result.object);
  }

  return modified;
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

  for(const auto &entry : map.get_view())
  {
    out << entry.first << " () -> ";
    entry.second->output(out, ai, ns);
    out << "\n";
  }

  out << "}\n";
}

exprt abstract_environmentt::to_predicate() const
{
  if(is_bottom())
    return false_exprt();
  if(is_top())
    return true_exprt();

  exprt::operandst predicates;
  for(const auto &entry : map.get_view())
  {
    auto sym = entry.first;
    auto val = entry.second;
    auto pred = val->to_predicate(symbol_exprt(sym, val->type()));

    predicates.push_back(pred);
  }

  if(predicates.size() == 1)
    return predicates.front();

  sort_operands(predicates);
  return and_exprt(predicates);
}

bool abstract_environmentt::verify() const
{
  for(const auto &entry : map.get_view())
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
  for(const auto &entry : first.map.get_view())
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
  abstract_object_visitedt visited;
  for(auto const &object : map.get_view())
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
  return std::dynamic_pointer_cast<const abstract_value_objectt>(
    obj->unwrap_context());
}

bool is_value(const abstract_object_pointert &obj)
{
  return as_value(obj) != nullptr;
}

static auto inverse_operations =
  std::map<irep_idt, irep_idt>{{ID_equal, ID_notequal},
                               {ID_notequal, ID_equal},
                               {ID_le, ID_gt},
                               {ID_lt, ID_ge},
                               {ID_ge, ID_lt},
                               {ID_gt, ID_le}};

static exprt invert_result(const exprt &result)
{
  if(!result.is_boolean())
    return result;

  if(result.is_true())
    return false_exprt();
  return true_exprt();
}

static exprt invert_expr(const exprt &expr)
{
  auto expr_id = expr.id();

  auto inverse_operation = inverse_operations.find(expr_id);
  if(inverse_operation == inverse_operations.end())
    return nil_exprt();

  auto relation_expr = to_binary_relation_expr(expr);
  auto inverse_op = inverse_operation->second;
  return binary_relation_exprt(
    relation_expr.lhs(), inverse_op, relation_expr.rhs());
}

void prune_assign(
  abstract_environmentt &env,
  const abstract_object_pointert &previous,
  const exprt &destination,
  abstract_object_pointert obj,
  const namespacet &ns)
{
  auto context =
    std::dynamic_pointer_cast<const context_abstract_objectt>(previous);
  if(context != nullptr)
    obj = context->envelop(obj);
  env.assign(destination, obj, ns);
}

exprt assume_not(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns)
{
  auto const &not_expr = to_not_expr(expr);

  auto inverse_expression = invert_expr(not_expr.op());
  if(inverse_expression.is_not_nil())
    return env.do_assume(inverse_expression, ns);

  auto result = env.do_assume(not_expr.op(), ns);
  return invert_result(result);
}

exprt assume_and(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns)
{
  auto and_expr = to_and_expr(expr);
  bool nil = false;
  for(auto const &operand : and_expr.operands())
  {
    auto result = env.do_assume(operand, ns);
    if(result.is_false())
      return result;
    nil |= result.is_nil();
  }
  if(nil)
    return nil_exprt();
  return true_exprt();
}

exprt assume_or(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns)
{
  auto or_expr = to_or_expr(expr);

  auto negated_operands = exprt::operandst{};
  for(auto const &operand : or_expr.operands())
    negated_operands.push_back(invert_expr(operand));

  auto result = assume_and(env, and_exprt(negated_operands), ns);
  return invert_result(result);
}

struct left_and_right_valuest
{
  exprt lhs;
  exprt rhs;
  abstract_object_pointert left;
  abstract_object_pointert right;

  constant_interval_exprt left_interval() const
  {
    return as_value(left)->to_interval();
  }
  constant_interval_exprt right_interval() const
  {
    return as_value(right)->to_interval();
  }

  bool are_bad() const
  {
    return left == nullptr || right == nullptr ||
           (left->is_top() && right->is_top()) || !is_value(left) ||
           !is_value(right);
  }

  bool has_top() const
  {
    return left->is_top() || right->is_top();
  }
};

left_and_right_valuest eval_operands_as_values(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns)
{
  auto const &relationship_expr = to_binary_expr(expr);

  auto lhs = relationship_expr.lhs();
  auto rhs = relationship_expr.rhs();
  auto left = env.eval(lhs, ns);
  auto right = env.eval(rhs, ns);

  if(left->is_top() && right->is_top())
    return {};

  return {lhs, rhs, left, right};
}

exprt assume_eq_unbounded(
  abstract_environmentt &env,
  const left_and_right_valuest &operands,
  const namespacet &ns)
{
  if(operands.left->is_top() && is_assignable(operands.lhs))
  {
    // TOP == x
    auto constrained = std::make_shared<interval_abstract_valuet>(
      operands.right_interval(), env, ns);
    prune_assign(env, operands.left, operands.lhs, constrained, ns);
  }
  if(operands.right->is_top() && is_assignable(operands.rhs))
  {
    // x == TOP
    auto constrained = std::make_shared<interval_abstract_valuet>(
      operands.left_interval(), env, ns);
    prune_assign(env, operands.right, operands.rhs, constrained, ns);
  }
  return true_exprt();
}

exprt assume_eq(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns)
{
  auto operands = eval_operands_as_values(env, expr, ns);

  if(operands.are_bad())
    return nil_exprt();

  if(operands.has_top())
    return assume_eq_unbounded(env, operands, ns);

  auto meet = operands.left->meet(operands.right);

  if(meet->is_bottom())
    return false_exprt();

  if(is_assignable(operands.lhs))
    prune_assign(env, operands.left, operands.lhs, meet, ns);
  if(is_assignable(operands.rhs))
    prune_assign(env, operands.right, operands.rhs, meet, ns);
  return true_exprt();
}

exprt assume_noteq(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns)
{
  auto const &notequal_expr = to_binary_expr(expr);

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

exprt assume_less_than_unbounded(
  abstract_environmentt &env,
  const left_and_right_valuest &operands,
  const namespacet &ns)
{
  if(operands.left->is_top() && is_assignable(operands.lhs))
  {
    // TOP < x, so prune range is min->right.upper
    auto pruned_expr = constant_interval_exprt(
      min_exprt(operands.left->type()),
      operands.right_interval().get_upper(),
      operands.left->type());
    auto constrained =
      std::make_shared<interval_abstract_valuet>(pruned_expr, env, ns);
    prune_assign(env, operands.left, operands.lhs, constrained, ns);
  }
  if(operands.right->is_top() && is_assignable(operands.rhs))
  {
    // x < TOP, so prune range is left.lower->max
    auto pruned_expr = constant_interval_exprt(
      operands.left_interval().get_lower(),
      max_exprt(operands.right->type()),
      operands.right->type());
    auto constrained =
      std::make_shared<interval_abstract_valuet>(pruned_expr, env, ns);
    prune_assign(env, operands.right, operands.rhs, constrained, ns);
  }

  return true_exprt();
}

exprt assume_less_than(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns)
{
  auto operands = eval_operands_as_values(env, expr, ns);
  if(operands.are_bad())
    return nil_exprt();

  if(operands.has_top())
    return assume_less_than_unbounded(env, operands, ns);

  auto left_interval = operands.left_interval();
  auto right_interval = operands.right_interval();

  const auto &left_lower = left_interval.get_lower();
  const auto &right_upper = right_interval.get_upper();

  auto reduced_le_expr =
    binary_relation_exprt(left_lower, expr.id(), right_upper);
  auto result = env.eval(reduced_le_expr, ns)->to_constant();
  if(result.is_true())
  {
    if(is_assignable(operands.lhs))
    {
      auto pruned_upper = constant_interval_exprt::get_min(
        left_interval.get_upper(), right_upper);
      auto constrained =
        as_value(operands.left)->constrain(left_lower, pruned_upper);
      prune_assign(env, operands.left, operands.lhs, constrained, ns);
    }
    if(is_assignable(operands.rhs))
    {
      auto pruned_lower = constant_interval_exprt::get_max(
        left_lower, right_interval.get_lower());
      auto constrained =
        as_value(operands.right)->constrain(pruned_lower, right_upper);
      prune_assign(env, operands.right, operands.rhs, constrained, ns);
    }
  }
  return result;
}

static auto symmetric_operations =
  std::map<irep_idt, irep_idt>{{ID_ge, ID_le}, {ID_gt, ID_lt}};

exprt assume_greater_than(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns)
{
  auto const &gt_expr = to_binary_expr(expr);

  auto symmetric_op = symmetric_operations[gt_expr.id()];
  auto symmetric_expr =
    binary_relation_exprt(gt_expr.rhs(), symmetric_op, gt_expr.lhs());

  return assume_less_than(env, symmetric_expr, ns);
}
