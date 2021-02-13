/*******************************************************************\

 Module: analyses variable-sensitivity intervals

 Author: Diffblue Ltd.

\*******************************************************************/

#include <limits.h>
#include <ostream>

#include <util/invariant.h>
#include <util/std_expr.h>

#include "abstract_environment.h"

#include "context_abstract_object.h"
#include "interval_abstract_value.h"

class interval_index_ranget : public index_ranget
{
public:
  interval_index_ranget(
    const constant_interval_exprt &interval,
    const namespacet &n)
    : index(nil_exprt()),
      next(interval.get_lower()),
      upper(interval.get_upper()),
      ns(n)
  {
  }

  const exprt &current() const override
  {
    return index;
  }
  bool advance_to_next() override
  {
    index = next;
    next = next_element(next, ns);
    return simplify_expr(binary_predicate_exprt(index, ID_le, upper), ns)
      .is_true();
  }

private:
  static exprt next_element(const exprt &cur, const namespacet &ns)
  {
    return simplify_expr(plus_exprt(cur, from_integer(1, cur.type())), ns);
  }

  exprt index;
  exprt next;
  exprt upper;
  const namespacet &ns;
};

static index_range_ptrt make_interval_index_range(
  const constant_interval_exprt &interval,
  const namespacet &n)
{
  return std::make_shared<interval_index_ranget>(interval, n);
}

static inline exprt look_through_casts(exprt e)
{
  while(e.id() == ID_typecast)
  {
    e = to_typecast_expr(e).op();
  }
  return e;
}

static inline bool
bvint_value_is_max(const typet &type, const mp_integer &value)
{
  PRECONDITION(type.id() == ID_signedbv || type.id() == ID_unsignedbv);
  if(type.id() == ID_signedbv)
  {
    return to_signedbv_type(type).largest() == value;
  }
  else
  {
    return to_unsignedbv_type(type).largest() == value;
  }
}

static inline bool
bvint_value_is_min(const typet &type, const mp_integer &value)
{
  PRECONDITION(type.id() == ID_signedbv || type.id() == ID_unsignedbv);
  if(type.id() == ID_signedbv)
  {
    return to_signedbv_type(type).smallest() == value;
  }
  else
  {
    return to_unsignedbv_type(type).smallest() == value;
  }
}

static inline constant_interval_exprt
interval_from_x_le_value(const exprt &value)
{
  return constant_interval_exprt(min_exprt(value.type()), value);
}

static inline constant_interval_exprt
interval_from_x_ge_value(const exprt &value)
{
  return constant_interval_exprt(value, max_exprt(value.type()));
}

static inline mp_integer force_value_from_expr(const exprt &value)
{
  PRECONDITION(constant_interval_exprt::is_int(value.type()));
  optionalt<mp_integer> maybe_integer_value = numeric_cast<mp_integer>(value);
  INVARIANT(maybe_integer_value.has_value(), "Input has to have a value");
  return maybe_integer_value.value();
}

static inline constant_interval_exprt
interval_from_x_lt_value(const exprt &value)
{
  mp_integer integer_value = force_value_from_expr(value);
  if(!bvint_value_is_min(value.type(), integer_value))
    return constant_interval_exprt(
      min_exprt(value.type()), from_integer(integer_value - 1, value.type()));
  else
    return constant_interval_exprt::bottom(value.type());
}

static inline constant_interval_exprt
interval_from_x_gt_value(const exprt &value)
{
  mp_integer integer_value = force_value_from_expr(value);
  if(!bvint_value_is_max(value.type(), integer_value))
    return constant_interval_exprt(
      from_integer(integer_value + 1, value.type()), max_exprt(value.type()));
  else
    return constant_interval_exprt::bottom(value.type());
}

static inline bool represents_interval(exprt e)
{
  e = look_through_casts(e);
  return (e.id() == ID_constant_interval || e.id() == ID_constant);
}

static inline constant_interval_exprt make_interval_expr(exprt e)
{
  e = look_through_casts(e);
  if(e.id() == ID_constant_interval)
  {
    return to_constant_interval_expr(e);
  }
  else if(e.id() == ID_constant)
  {
    return constant_interval_exprt(e, e);
  }
  else
  {
    // not directly representable, so just return TOP
    return constant_interval_exprt(e.type());
  }
}

static inline irep_idt invert_relation(const irep_idt &relation)
{
  PRECONDITION(
    relation == ID_le || relation == ID_lt || relation == ID_ge ||
    relation == ID_gt || relation == ID_equal);
  if(relation == ID_le)
    return ID_ge;
  if(relation == ID_ge)
    return ID_le;
  if(relation == ID_lt)
    return ID_gt;
  if(relation == ID_gt)
    return ID_lt;
  return relation;
}

/// Builds an interval representing all values satisfying the input expression.
/// The expression is expected to be a comparison between an integer constant
/// and a variable (symbol)
/// \param e the relation expression that should be satisfied
/// \return the constant interval expression representing the values
static inline constant_interval_exprt interval_from_relation(const exprt &e)
{
  PRECONDITION(e.operands().size() == 2);
  const auto &relation = e.id();
  const auto &binary_e = to_binary_expr(e);
  const auto &lhs = binary_e.lhs();
  const auto &rhs = binary_e.rhs();
  PRECONDITION(
    relation == ID_le || relation == ID_lt || relation == ID_ge ||
    relation == ID_gt || relation == ID_equal);
  PRECONDITION(lhs.id() == ID_constant || lhs.id() == ID_symbol);
  PRECONDITION(rhs.id() == ID_constant || rhs.id() == ID_symbol);
  PRECONDITION(lhs.id() != rhs.id());

  const auto the_constant_part_of_the_relation =
    (rhs.id() == ID_symbol ? lhs : rhs);
  const auto maybe_inverted_relation =
    (rhs.id() == ID_symbol ? invert_relation(relation) : relation);

  if(maybe_inverted_relation == ID_le)
    return interval_from_x_le_value(the_constant_part_of_the_relation);
  if(maybe_inverted_relation == ID_lt)
    return interval_from_x_lt_value(the_constant_part_of_the_relation);
  if(maybe_inverted_relation == ID_ge)
    return interval_from_x_ge_value(the_constant_part_of_the_relation);
  if(maybe_inverted_relation == ID_gt)
    return interval_from_x_gt_value(the_constant_part_of_the_relation);
  INVARIANT(
    maybe_inverted_relation == ID_equal, "We excluded other cases above");
  return constant_interval_exprt(
    the_constant_part_of_the_relation, the_constant_part_of_the_relation);
}

interval_abstract_valuet::interval_abstract_valuet(const typet &t)
  : abstract_value_objectt(t), interval(t)
{
}

interval_abstract_valuet::interval_abstract_valuet(
  const typet &t,
  bool tp,
  bool bttm)
  : abstract_value_objectt(t, tp, bttm), interval(t)
{
}

interval_abstract_valuet::interval_abstract_valuet(
  const constant_interval_exprt &e)
  : abstract_value_objectt(e.type(), e.is_top(), e.is_bottom()), interval(e)
{
}

interval_abstract_valuet::interval_abstract_valuet(
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : interval_abstract_valuet(
      represents_interval(e)
        ? make_interval_expr(e)
        : (e.operands().size() == 2 ? interval_from_relation(e)
                                    : constant_interval_exprt(e.type())))
{
}

exprt interval_abstract_valuet::to_constant() const
{
  // Attempt to reduce this interval to a constant expression
  if(interval.is_single_value_interval())
  {
    // Interval is the equivalent of a constant, so reduce it to a constant
    return to_constant_expr(interval.get_lower());
  }
  return abstract_objectt::to_constant();
#if 0
  if(!is_top() && !is_bottom())
  {
    return this->interval;
  }
  else
  {
    return abstract_objectt::to_constant();
  }
#endif
}

abstract_object_pointert interval_abstract_valuet::expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  std::size_t num_operands = expr.operands().size();
  PRECONDITION(operands.size() == num_operands);

  std::vector<sharing_ptrt<interval_abstract_valuet>> interval_operands;

  for(const auto &op : operands)
  {
    auto iav = std::dynamic_pointer_cast<const interval_abstract_valuet>(op);
    if(!iav)
    {
      // The operand isn't an interval - if it's an integral constant we can
      // convert it into an interval.

      if(constant_interval_exprt::is_int(op->type()))
      {
        const auto op_as_constant = op->to_constant();
        if(op_as_constant.is_nil())
        {
          auto top_object =
            environment.abstract_object_factory(expr.type(), ns, true, false);
          auto top_context_object =
            std::dynamic_pointer_cast<const context_abstract_objectt>(
              top_object);
          CHECK_RETURN(top_context_object);
          return top_context_object->get_child();
        }
        const auto ivop =
          environment.abstract_object_factory(op->type(), op_as_constant, ns);
        const auto ivop_context =
          std::dynamic_pointer_cast<const context_abstract_objectt>(ivop);
        if(ivop_context)
        {
          iav = std::dynamic_pointer_cast<const interval_abstract_valuet>(
            ivop_context->get_child());
        }
        else
          iav = std::dynamic_pointer_cast<const interval_abstract_valuet>(ivop);
      }
      CHECK_RETURN(
        !std::dynamic_pointer_cast<const context_abstract_objectt>(iav));

      if(!iav)
      {
        // If we could not convert the operand into an interval,
        // e.g. if its type is not something we can represent as an interval,
        // try dispatching the expression_transform under that type instead.
        return op->expression_transform(expr, operands, environment, ns);
      }
    }

    INVARIANT(iav, "Should be an interval abstract value");
    interval_operands.push_back(iav);
  }

  if(num_operands == 0)
    return environment.abstract_object_factory(expr.type(), ns, true, false);

  if(expr.id() == ID_if)
    return evaluate_conditional(expr, interval_operands, environment, ns);

  if(num_operands == 1)
    return evaluate_unary_expr(expr, interval_operands, environment, ns);

  constant_interval_exprt result = interval_operands[0]->interval;

  for(size_t opIndex = 1; opIndex != interval_operands.size(); ++opIndex)
  {
    auto &interval_next = interval_operands[opIndex]->interval;
    result = result.eval(expr.id(), interval_next);
  }

  INVARIANT(
    result.type() == expr.type(),
    "Type of result interval should match expression type");
  return environment.abstract_object_factory(expr.type(), result, ns);
}

abstract_object_pointert interval_abstract_valuet::evaluate_conditional(
  const exprt &expr,
  const std::vector<interval_abstract_value_pointert> &interval_operands,
  const abstract_environmentt &env,
  const namespacet &ns)
{
  auto const &condition_interval = interval_operands[0]->interval;
  auto const &true_interval = interval_operands[1]->interval;
  auto const &false_interval = interval_operands[2]->interval;

  auto condition_result = condition_interval.is_definitely_true();

  if(condition_result.is_unknown())
  {
    // Value of the condition is both true and false, so
    // combine the intervals of both the true and false expressions
    return env.abstract_object_factory(
      expr.type(),
      constant_interval_exprt(
        constant_interval_exprt::get_min(
          true_interval.get_lower(), false_interval.get_lower()),
        constant_interval_exprt::get_max(
          true_interval.get_upper(), false_interval.get_upper())),
      ns);
  }

  return condition_result.is_true()
           ? env.abstract_object_factory(
               true_interval.type(), true_interval, ns)
           : env.abstract_object_factory(
               false_interval.type(), false_interval, ns);
}

abstract_object_pointert interval_abstract_valuet::evaluate_unary_expr(
  const exprt &expr,
  const std::vector<interval_abstract_value_pointert> &interval_operands,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  const constant_interval_exprt &operand_expr = interval_operands[0]->interval;

  if(expr.id() == ID_typecast)
  {
    const typecast_exprt &tce = to_typecast_expr(expr);

    const constant_interval_exprt &new_interval =
      operand_expr.typecast(tce.type());

    INVARIANT(
      new_interval.type() == expr.type(),
      "Type of result interval should match expression type");

    return environment.abstract_object_factory(tce.type(), new_interval, ns);
  }

  const constant_interval_exprt &interval_result = operand_expr.eval(expr.id());
  INVARIANT(
    interval_result.type() == expr.type(),
    "Type of result interval should match expression type");
  return environment.abstract_object_factory(expr.type(), interval_result, ns);
}

void interval_abstract_valuet::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  if(!is_top() && !is_bottom())
  {
    std::string lower_string;
    std::string upper_string;

    if(interval.get_lower().id() == ID_min)
    {
      lower_string = "-INF";
    }
    else
    {
      INVARIANT(
        interval.get_lower().id() == ID_constant,
        "We only support constant limits");
      lower_string =
        id2string(to_constant_expr(interval.get_lower()).get_value());
    }

    if(interval.get_upper().id() == ID_max)
    {
      upper_string = "+INF";
    }
    else
    {
      INVARIANT(
        interval.get_lower().id() == ID_constant,
        "We only support constant limits");
      upper_string =
        id2string(to_constant_expr(interval.get_upper()).get_value());
    }

    out << "[" << lower_string << ", " << upper_string << "]";
  }
  else
  {
    abstract_objectt::output(out, ai, ns);
  }
}

abstract_object_pointert
interval_abstract_valuet::merge(abstract_object_pointert other) const
{
  interval_abstract_value_pointert cast_other =
    std::dynamic_pointer_cast<const interval_abstract_valuet>(other);
  if(cast_other)
  {
    return merge_intervals(cast_other);
  }
  else
  {
    return abstract_objectt::merge(other);
  }
}

/// Merge another interval abstract object with this one
/// \param other The interval abstract object to merge with
/// \return This if the other interval is subsumed by this,
///          other if this is subsumed by other.
///          Otherwise, a new interval abstract object
///          with the smallest interval that subsumes both
///          this and other
abstract_object_pointert interval_abstract_valuet::merge_intervals(
  interval_abstract_value_pointert other) const
{
  if(is_bottom() || other->interval.contains(interval))
  {
    return other;
  }
  else if(other->is_bottom() || interval.contains(other->interval))
  {
    return shared_from_this();
  }
  else
  {
    return std::make_shared<interval_abstract_valuet>(constant_interval_exprt(
      constant_interval_exprt::get_min(
        interval.get_lower(), other->interval.get_lower()),
      constant_interval_exprt::get_max(
        interval.get_upper(), other->interval.get_upper())));
  }
}

abstract_object_pointert
interval_abstract_valuet::meet(const abstract_object_pointert &other) const
{
  interval_abstract_value_pointert cast_other =
    std::dynamic_pointer_cast<const interval_abstract_valuet>(other);
  if(cast_other)
  {
    return meet_intervals(cast_other);
  }
  else
  {
    return abstract_objectt::meet(other);
  }
}

/// Meet another interval abstract object with this one
/// \param other The interval abstract object to meet with
/// \return This if the other interval subsumes this,
///          other if this subsumes other.
///          Otherwise, a new interval abstract object
///          with the intersection interval (of this and other)
abstract_object_pointert interval_abstract_valuet::meet_intervals(
  interval_abstract_value_pointert other) const
{
  if(is_bottom() || other->interval.contains(interval))
  {
    return shared_from_this();
  }
  else if(other->is_bottom() || interval.contains(other->interval))
  {
    return other;
  }
  else
  {
    auto lower_bound = constant_interval_exprt::get_max(
      interval.get_lower(), other->interval.get_lower());
    auto upper_bound = constant_interval_exprt::get_min(
      interval.get_upper(), other->interval.get_upper());

    if(constant_interval_exprt::less_than(upper_bound, lower_bound))
      return std::make_shared<interval_abstract_valuet>(
        interval.type(), false, true);
    return std::make_shared<interval_abstract_valuet>(
      constant_interval_exprt(lower_bound, upper_bound));
  }
}

index_range_ptrt
interval_abstract_valuet::index_range(const namespacet &ns) const
{
  if(is_top() || is_bottom() || interval.is_top() || interval.is_bottom())
    return make_empty_index_range();
  if(interval.get_lower().id() == ID_min || interval.get_upper().id() == ID_max)
    return make_empty_index_range();

  return make_interval_index_range(interval, ns);
}

const constant_interval_exprt &interval_abstract_valuet::get_interval() const
{
  return interval;
}

void interval_abstract_valuet::get_statistics(
  abstract_object_statisticst &statistics,
  abstract_object_visitedt &visited,
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  abstract_objectt::get_statistics(statistics, visited, env, ns);
  ++statistics.number_of_interval_abstract_objects;
  if(interval.is_single_value_interval())
  {
    ++statistics.number_of_single_value_intervals;
  }
  statistics.objects_memory_usage += memory_sizet::from_bytes(sizeof(*this));
}
