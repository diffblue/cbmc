/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: diffblue

\*******************************************************************/

/// \file
/// Value Set Abstract Object

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/context_abstract_object.h>
#include <analyses/variable-sensitivity/interval_abstract_value.h>
#include <analyses/variable-sensitivity/value_set_abstract_object.h>
#include <analyses/variable-sensitivity/widened_range.h>

#include <util/arith_tools.h>
#include <util/make_unique.h>
#include <util/simplify_expr.h>

#include <algorithm>

static index_range_implementation_ptrt
make_value_set_index_range(const std::set<exprt> &vals);

class value_set_index_ranget : public index_range_implementationt
{
public:
  explicit value_set_index_ranget(const std::set<exprt> &vals)
    : values(vals), cur(), next(values.begin())
  {
    PRECONDITION(!values.empty());
  }

  const exprt &current() const override
  {
    return cur;
  }
  bool advance_to_next() override
  {
    if(next == values.end())
      return false;

    cur = *next;
    ++next;
    return true;
  }
  index_range_implementation_ptrt reset() const override
  {
    return make_value_set_index_range(values);
  }

private:
  std::set<exprt> values;
  exprt cur;
  std::set<exprt>::const_iterator next;
};

static index_range_implementation_ptrt
make_value_set_index_range(const std::set<exprt> &vals)
{
  return util_make_unique<value_set_index_ranget>(vals);
}

static value_range_implementation_ptrt
make_value_set_value_range(const abstract_object_sett &vals);

class value_set_value_ranget : public value_range_implementationt
{
public:
  explicit value_set_value_ranget(const abstract_object_sett &vals)
    : values(vals), cur(), next(values.begin())
  {
    PRECONDITION(!values.empty());
  }

  const abstract_object_pointert &current() const override
  {
    return cur;
  }
  bool advance_to_next() override
  {
    if(next == values.end())
      return false;

    cur = *next;
    ++next;
    return true;
  }
  value_range_implementation_ptrt reset() const override
  {
    return make_value_set_value_range(values);
  }

private:
  const abstract_object_sett &values;
  abstract_object_pointert cur;
  abstract_object_sett::const_iterator next;
};

static value_range_implementation_ptrt
make_value_set_value_range(const abstract_object_sett &vals)
{
  return util_make_unique<value_set_value_ranget>(vals);
}

static abstract_object_sett
unwrap_and_extract_values(const abstract_object_sett &values);

/// Helper for converting singleton value sets into its only value.
/// \p maybe_singleton: either a set of abstract values or a single value
/// \return an abstract value without context
static abstract_object_pointert
maybe_extract_single_value(const abstract_object_pointert &maybe_singleton);

static bool are_any_top(const abstract_object_sett &set);
static bool is_set_extreme(const typet &type, const abstract_object_sett &set);

static abstract_object_sett compact_values(const abstract_object_sett &values);
static abstract_object_sett
non_destructive_compact(const abstract_object_sett &values);
static abstract_object_sett widen_value_set(
  const abstract_object_sett &values,
  const constant_interval_exprt &lhs,
  const constant_interval_exprt &rhs);

value_set_abstract_objectt::value_set_abstract_objectt(const typet &type)
  : abstract_value_objectt(type)
{
  values.insert(std::make_shared<constant_abstract_valuet>(type));
  verify();
}

value_set_abstract_objectt::value_set_abstract_objectt(
  const typet &type,
  bool top,
  bool bottom)
  : abstract_value_objectt(type, top, bottom)
{
  values.insert(std::make_shared<constant_abstract_valuet>(type, top, bottom));
  verify();
}

value_set_abstract_objectt::value_set_abstract_objectt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_value_objectt(expr.type(), false, false)
{
  values.insert(
    std::make_shared<constant_abstract_valuet>(expr, environment, ns));
  verify();
}

abstract_object_pointert value_set_abstract_objectt::make_value_set(
  const abstract_object_sett &initial_values)
{
  PRECONDITION(!initial_values.empty());

  auto values = unwrap_and_extract_values(initial_values);

  values = compact_values(values);

  const auto &type = values.first()->type();
  auto value_set =
    std::make_shared<value_set_abstract_objectt>(type, false, false);
  value_set->set_values(values);
  return value_set;
}

index_range_implementation_ptrt
value_set_abstract_objectt::index_range_implementation(
  const namespacet &ns) const
{
  if(values.empty())
    return make_indeterminate_index_range();

  std::set<exprt> flattened;
  for(const auto &o : values)
  {
    const auto &v = as_value(o);
    for(auto e : v->index_range(ns))
      flattened.insert(e);
  }

  return make_value_set_index_range(flattened);
}

value_range_implementation_ptrt
value_set_abstract_objectt::value_range_implementation() const
{
  return make_value_set_value_range(values);
}

exprt value_set_abstract_objectt::to_constant() const
{
  verify();

  if(values.size() == 1)
    return values.first()->to_constant();

  auto interval = to_interval();
  if(interval.is_single_value_interval())
    return interval.get_lower();

  return abstract_objectt::to_constant();
}

constant_interval_exprt value_set_abstract_objectt::to_interval() const
{
  return values.to_interval();
}

abstract_object_pointert value_set_abstract_objectt::merge_with_value(
  const abstract_value_pointert &other,
  const widen_modet &widen_mode) const
{
  auto union_values = !is_bottom() ? values : abstract_object_sett{};

  auto other_value_set = std::dynamic_pointer_cast<const value_set_tag>(other);
  if(other_value_set)
    union_values.insert(other_value_set->get_values());
  else
    union_values.insert(other);

  auto has_values = [](const abstract_object_pointert &v) {
    return !v->is_top() && !v->is_bottom();
  };

  if(
    widen_mode == widen_modet::could_widen && has_values(shared_from_this()) &&
    has_values(other))
  {
    union_values =
      widen_value_set(union_values, to_interval(), other->to_interval());
  }

  return resolve_values(union_values);
}

abstract_object_pointert value_set_abstract_objectt::meet_with_value(
  const abstract_value_pointert &other) const
{
  if(other->is_bottom())
    return shared_from_this();

  auto meet_values = abstract_object_sett{};

  if(is_bottom())
    meet_values.insert(other);
  else
  {
    auto this_interval = to_interval();
    auto other_interval = other->to_interval();

    auto lower_bound = constant_interval_exprt::get_max(
      this_interval.get_lower(), other_interval.get_lower());
    auto upper_bound = constant_interval_exprt::get_min(
      this_interval.get_upper(), other_interval.get_upper());

    // if the interval is valid, we have a meet!
    if(constant_interval_exprt::less_than_or_equal(lower_bound, upper_bound))
    {
      auto meet_interval = constant_interval_exprt(lower_bound, upper_bound);
      abstract_object_pointert meet_value =
        std::make_shared<interval_abstract_valuet>(meet_interval);
      if(meet_interval.is_single_value_interval())
        meet_value = std::make_shared<constant_abstract_valuet>(lower_bound);
      meet_values.insert(meet_value);
    }
  }

  if(meet_values.empty()) // no meet :(
    return std::make_shared<value_set_abstract_objectt>(type(), false, true);

  return resolve_values(meet_values);
}

abstract_object_pointert value_set_abstract_objectt::resolve_values(
  const abstract_object_sett &new_values) const
{
  PRECONDITION(!new_values.empty());

  if(new_values == values)
    return shared_from_this();

  return make_value_set(new_values);
}

void value_set_abstract_objectt::set_top_internal()
{
  values.clear();
  values.insert(std::make_shared<constant_abstract_valuet>(type()));
}

void value_set_abstract_objectt::set_values(
  const abstract_object_sett &other_values)
{
  PRECONDITION(!other_values.empty());
  if(are_any_top(other_values) || is_set_extreme(type(), other_values))
  {
    set_top();
  }
  else
  {
    set_not_top();
    values = other_values;
  }
  set_not_bottom();
  verify();
}

abstract_value_pointert value_set_abstract_objectt::constrain(
  const exprt &lower,
  const exprt &upper) const
{
  using cie = constant_interval_exprt;

  auto constrained_values = abstract_object_sett{};

  for(auto const &value : unwrap_and_extract_values(values))
  {
    auto constrained = as_value(value)->constrain(lower, upper);
    auto constrained_interval = constrained->to_interval();

    if(cie::less_than(constrained_interval.get_lower(), lower))
      continue;
    if(cie::greater_than(constrained_interval.get_upper(), upper))
      continue;

    constrained_values.insert(constrained);
  }

  return as_value(resolve_values(constrained_values));
}

exprt value_set_abstract_objectt::to_predicate_internal(const exprt &name) const
{
  auto compacted = non_destructive_compact(values);
  if(compacted.size() == 1)
    return compacted.first()->to_predicate(name);

  auto all_predicates = exprt::operandst{};
  std::transform(
    compacted.begin(),
    compacted.end(),
    std::back_inserter(all_predicates),
    [&name](const abstract_object_pointert &value) {
      return value->to_predicate(name);
    });
  std::sort(all_predicates.begin(), all_predicates.end());

  return or_exprt(all_predicates);
}

void value_set_abstract_objectt::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  if(is_top())
  {
    out << "TOP";
  }
  else if(is_bottom())
  {
    out << "BOTTOM";
  }
  else
  {
    out << "value-set-begin: ";

    values.output(out, ai, ns);

    out << " :value-set-end";
  }
}

static abstract_object_sett
unwrap_and_extract_values(const abstract_object_sett &values)
{
  abstract_object_sett unwrapped_values;
  for(auto const &value : values)
    unwrapped_values.insert(maybe_extract_single_value(value));

  return unwrapped_values;
}

static abstract_object_pointert
maybe_extract_single_value(const abstract_object_pointert &maybe_singleton)
{
  auto const &value_as_set = std::dynamic_pointer_cast<const value_set_tag>(
    maybe_singleton->unwrap_context());
  if(value_as_set)
  {
    PRECONDITION(value_as_set->get_values().size() == 1);
    PRECONDITION(!std::dynamic_pointer_cast<const context_abstract_objectt>(
      value_as_set->get_values().first()));

    return value_as_set->get_values().first();
  }
  else
    return maybe_singleton;
}

static bool are_any_top(const abstract_object_sett &set)
{
  return std::find_if(
           set.begin(), set.end(), [](const abstract_object_pointert &value) {
             return value->is_top();
           }) != set.end();
}

using set_predicate_fn = std::function<bool(const abstract_value_objectt &)>;
static bool set_contains(const abstract_object_sett &set, set_predicate_fn pred)
{
  return std::find_if(
           set.begin(),
           set.end(),
           [&pred](const abstract_object_pointert &obj) {
             const auto &value =
               std::dynamic_pointer_cast<const abstract_value_objectt>(obj);
             return pred(*value);
           }) != set.end();
}

static bool set_has_extremes(
  const abstract_object_sett &set,
  set_predicate_fn lower_fn,
  set_predicate_fn upper_fn)
{
  bool has_lower = set_contains(set, lower_fn);
  if(!has_lower)
    return false;

  bool has_upper = set_contains(set, upper_fn);
  return has_upper;
}

static bool is_set_extreme(const typet &type, const abstract_object_sett &set)
{
  if(type.id() == ID_bool)
  {
    return set_has_extremes(
      set,
      [](const abstract_value_objectt &value) {
        auto c = value.to_constant();
        return c.is_false() || (c.id() == ID_min);
      },
      [](const abstract_value_objectt &value) {
        auto c = value.to_constant();
        return c.is_true() || (c.id() == ID_max);
      });
  }

  if(type.id() == ID_c_bool)
  {
    return set_has_extremes(
      set,
      [](const abstract_value_objectt &value) {
        auto c = value.to_constant();
        return c.is_zero() || (c.id() == ID_min);
      },
      [](const abstract_value_objectt &value) {
        auto c = value.to_constant();
        return c.is_one() || (c.id() == ID_max);
      });
  }

  return false;
}

/////////////////
static abstract_object_sett
non_destructive_compact(const abstract_object_sett &values);
static abstract_object_sett
destructive_compact(abstract_object_sett values, int slice = 3);
static bool value_is_not_contained_in(
  const abstract_object_pointert &object,
  const std::vector<constant_interval_exprt> &intervals);

static abstract_object_sett compact_values(const abstract_object_sett &values)
{
  if(values.size() <= value_set_abstract_objectt::max_value_set_size)
    return values;

  auto compacted = non_destructive_compact(values);
  if(compacted.size() <= value_set_abstract_objectt::max_value_set_size)
    return compacted;

  compacted = destructive_compact(values);

  return compacted;
}

static exprt eval_expr(const exprt &e);
static bool is_eq(const exprt &lhs, const exprt &rhs);
static bool is_le(const exprt &lhs, const exprt &rhs);
static abstract_object_sett collapse_values_in_intervals(
  const abstract_object_sett &values,
  const std::vector<constant_interval_exprt> &intervals);
static void
collapse_overlapping_intervals(std::vector<constant_interval_exprt> &intervals);

static std::vector<constant_interval_exprt>
collect_intervals(const abstract_object_sett &values)
{
  auto intervals = std::vector<constant_interval_exprt>{};
  for(auto const &object : values)
  {
    auto value =
      std::dynamic_pointer_cast<const abstract_value_objectt>(object);
    auto as_expr = value->to_interval();
    if(!as_expr.is_single_value_interval())
      intervals.push_back(as_expr);
  }

  collapse_overlapping_intervals(intervals);

  return intervals;
}

void collapse_overlapping_intervals(
  std::vector<constant_interval_exprt> &intervals)
{
  std::sort(
    intervals.begin(),
    intervals.end(),
    [](constant_interval_exprt const &lhs, constant_interval_exprt const &rhs) {
      if(is_eq(lhs.get_lower(), rhs.get_lower()))
        return is_le(lhs.get_upper(), rhs.get_upper());
      return is_le(lhs.get_lower(), rhs.get_lower());
    });

  size_t index = 1;
  while(index < intervals.size())
  {
    auto &lhs = intervals[index - 1];
    auto &rhs = intervals[index];

    bool overlap = is_le(rhs.get_lower(), lhs.get_upper());
    if(overlap)
    {
      auto upper = is_le(lhs.get_upper(), rhs.get_upper()) ? rhs.get_upper()
                                                           : lhs.get_upper();
      auto expanded = constant_interval_exprt(lhs.get_lower(), upper);
      lhs = expanded;
      intervals.erase(intervals.begin() + index);
    }
    else
      ++index;
  }
}

static abstract_object_sett
non_destructive_compact(const abstract_object_sett &values)
{
  auto intervals = collect_intervals(values);
  if(intervals.empty())
    return values;

  return collapse_values_in_intervals(values, intervals);
}

static abstract_object_sett collapse_values_in_intervals(
  const abstract_object_sett &values,
  const std::vector<constant_interval_exprt> &intervals)
{
  auto collapsed = abstract_object_sett{};
  // for each value, including the intervals
  // keep it if it is not in any of the intervals
  std::copy_if(
    values.begin(),
    values.end(),
    std::back_inserter(collapsed),
    [&intervals](const abstract_object_pointert &object) {
      return value_is_not_contained_in(object, intervals);
    });
  std::transform(
    intervals.begin(),
    intervals.end(),
    std::back_inserter(collapsed),
    [](const constant_interval_exprt &interval) {
      return interval_abstract_valuet::make_interval(interval);
    });
  return collapsed;
}

static abstract_object_sett
destructive_compact(abstract_object_sett values, int slice)
{
  auto value_count = values.size();
  auto width = values.to_interval();
  auto slice_width = eval_expr(div_exprt(
    minus_exprt(width.get_upper(), width.get_lower()),
    from_integer(slice, width.type())));

  auto lower_boundary = eval_expr(plus_exprt(width.get_lower(), slice_width));
  auto upper_start = eval_expr(minus_exprt(width.get_upper(), slice_width));
  if(
    lower_boundary ==
    upper_start) // adjust boundary so intervals aren't immediately combined
    upper_start = eval_expr(
      plus_exprt(upper_start, from_integer(1, lower_boundary.type())));

  auto lower_slice = constant_interval_exprt(width.get_lower(), lower_boundary);
  auto upper_slice = constant_interval_exprt(upper_start, width.get_upper());

  values.insert(interval_abstract_valuet::make_interval(lower_slice));
  values.insert(interval_abstract_valuet::make_interval(upper_slice));

  auto compacted = non_destructive_compact(values);
  if(compacted.size() == value_count)
    return destructive_compact(compacted, --slice);

  return compacted;
} // destructive_compact

static bool value_is_not_contained_in(
  const abstract_object_pointert &object,
  const std::vector<constant_interval_exprt> &intervals)
{
  auto value = std::dynamic_pointer_cast<const abstract_value_objectt>(object);
  auto as_expr = value->to_interval();

  return std::none_of(
    intervals.begin(),
    intervals.end(),
    [&as_expr](const constant_interval_exprt &interval) {
      return interval.contains(as_expr);
    });
}

static exprt eval_expr(const exprt &e)
{
  auto symbol_table = symbol_tablet{};
  auto ns = namespacet{symbol_table};

  return simplify_expr(e, ns);
}

static bool is_eq(const exprt &lhs, const exprt &rhs)
{
  return constant_interval_exprt::equal(lhs, rhs);
}

static bool is_le(const exprt &lhs, const exprt &rhs)
{
  return constant_interval_exprt::less_than_or_equal(lhs, rhs);
}

static abstract_object_sett widen_value_set(
  const abstract_object_sett &values,
  const constant_interval_exprt &lhs,
  const constant_interval_exprt &rhs)
{
  if(lhs.contains(rhs))
    return values;

  auto widened_ends = std::vector<constant_interval_exprt>{};

  auto range = widened_ranget(lhs, rhs);

  // should extend lower bound?
  if(range.is_lower_widened)
  {
    auto extended_lower_bound =
      constant_interval_exprt(range.widened_lower_bound, range.lower_bound);

    widened_ends.push_back(extended_lower_bound);
    for(auto &obj : values)
    {
      auto value = std::dynamic_pointer_cast<const abstract_value_objectt>(obj);
      auto as_expr = value->to_interval();
      if(is_le(as_expr.get_lower(), range.lower_bound))
        widened_ends.push_back(as_expr);
    }
  }
  // should extend upper bound?
  if(range.is_upper_widened)
  {
    auto extended_upper_bound =
      constant_interval_exprt(range.upper_bound, range.widened_upper_bound);
    widened_ends.push_back(extended_upper_bound);
    for(auto &obj : values)
    {
      auto value = std::dynamic_pointer_cast<const abstract_value_objectt>(obj);
      auto as_expr = value->to_interval();
      if(is_le(range.upper_bound, as_expr.get_upper()))
        widened_ends.push_back(as_expr);
    }
  }

  collapse_overlapping_intervals(widened_ends);
  return collapse_values_in_intervals(values, widened_ends);
}
