/*******************************************************************\

 Module: analyses variable-sensitivity variable-sensitivity-value-set

 Author: Diffblue Ltd.

\*******************************************************************/

#include "value_set_abstract_value.h"

#include <ansi-c/expr2c.h>
#include <util/simplify_expr.h>

value_set_abstract_valuet::value_set_abstract_valuet(
  const typet &type,
  bool top,
  bool bottom)
  : abstract_objectt{type, top, bottom}, values{}
{
}

const value_set_abstract_valuet::valuest &
value_set_abstract_valuet::get_values() const
{
  PRECONDITION(!is_top());
  PRECONDITION(!is_bottom());
  return values;
}

abstract_object_pointert
value_set_abstract_valuet::merge(abstract_object_pointert other) const
{
  if(is_top())
  {
    return shared_from_this();
  }

  if(other->is_top())
  {
    return other;
  }

  if(is_bottom())
  {
    return other;
  }

  if(other->is_bottom())
  {
    return shared_from_this();
  }

  if(
    auto other_value_set =
      dynamic_cast<const value_set_abstract_valuet *>(other.get()))
  {
    valuest merged_values{values};
    auto const &other_values = other_value_set->get_values();
    merged_values.insert(other_values.begin(), other_values.end());
    return std::make_shared<value_set_abstract_valuet>(
      type(), std::move(merged_values));
  }
  return abstract_objectt::merge(other);
}

value_set_abstract_valuet::value_set_abstract_valuet(
  const typet &type,
  valuest values)
  : abstract_objectt{type, values.size() > max_value_set_size, values.empty()},
    values{std::move(values)}
{
  if(values.size() > max_value_set_size)
  {
    this->values.clear();
  }
}

value_set_abstract_valuet::value_set_abstract_valuet(
  exprt expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : value_set_abstract_valuet{expr.type(), valuest{expr}}
{
}

exprt value_set_abstract_valuet::to_constant() const
{
  if(!is_top() && !is_bottom() && values.size() == 1)
  {
    return *values.begin();
  }
  else
  {
    return nil_exprt{};
  }
}

void value_set_abstract_valuet::output(
  std::ostream &out,
  const class ai_baset &,
  const namespacet &ns) const
{
  if(is_bottom())
  {
    out << "BOTTOM";
    return;
  }
  else if(is_top())
  {
    out << "TOP";
    return;
  }

  std::vector<std::string> vals;
  for(const auto &elem : values)
  {
    vals.push_back(expr2c(elem, ns));
  }

  std::sort(vals.begin(), vals.end());

  out << "{ ";
  for(const auto &val : vals)
  {
    out << val << " ";
  }
  out << "}";
}

static void merge_all_possible_results(
  std::shared_ptr<const value_set_abstract_valuet> &out_value,
  const exprt &expr,
  const std::vector<const value_set_abstract_valuet *> &operand_value_sets,
  const namespacet &ns,
  std::vector<exprt> &operands_so_far)
{
  if(expr.operands().size() == operands_so_far.size())
  {
    exprt expr_with_evaluated_operands_filled_in = expr;
    expr_with_evaluated_operands_filled_in.operands() = operands_so_far;
    simplify(expr_with_evaluated_operands_filled_in, ns);
    if(expr_with_evaluated_operands_filled_in.is_constant())
    {
      auto post_merge = abstract_objectt::merge(
        out_value,
        std::make_shared<value_set_abstract_valuet>(
          expr.type(),
          value_set_abstract_valuet::valuest{
            expr_with_evaluated_operands_filled_in}));
      if(
        auto post_merge_casted =
          std::dynamic_pointer_cast<const value_set_abstract_valuet>(
            post_merge))
      {
        out_value = post_merge_casted;
        return;
      }
    }
    out_value = std::make_shared<value_set_abstract_valuet>(expr.type());
  }
  else
  {
    for(auto const &operand_value :
        operand_value_sets[operands_so_far.size()]->get_values())
    {
      operands_so_far.push_back(operand_value);
      merge_all_possible_results(
        out_value, expr, operand_value_sets, ns, operands_so_far);
      operands_so_far.pop_back();
    }
  }
}

static std::shared_ptr<const value_set_abstract_valuet>
merge_all_possible_results(
  const exprt &expr,
  const std::vector<const value_set_abstract_valuet *> &operand_value_sets,
  const namespacet &ns)
{
  const bool is_top = false;
  const bool is_bottom = true;
  auto result_abstract_value =
    std::make_shared<const value_set_abstract_valuet>(
      expr.type(), is_top, is_bottom);
  auto operands_so_far = std::vector<exprt>{};
  merge_all_possible_results(
    result_abstract_value, expr, operand_value_sets, ns, operands_so_far);
  return result_abstract_value;
}

abstract_object_pointert value_set_abstract_valuet::expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  // TODO possible special case handling for things like
  //  __CPROVER_rounding_mode where we know what valid values look like
  //  which we could make use of in place of TOP
  auto operand_value_sets = std::vector<const value_set_abstract_valuet *>{};
  for(auto const &possible_value_set : operands)
  {
    PRECONDITION(possible_value_set != nullptr);
    const auto as_value_set =
      dynamic_cast<const value_set_abstract_valuet *>(possible_value_set.get());
    if(
      as_value_set == nullptr || as_value_set->is_top() ||
      as_value_set->is_bottom())
    {
      return std::make_shared<value_set_abstract_valuet>(expr.type());
    }
    operand_value_sets.push_back(as_value_set);
  }
  return merge_all_possible_results(expr, operand_value_sets, ns);
}
