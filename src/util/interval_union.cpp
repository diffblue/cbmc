/*******************************************************************\

Module: Util

Author: Diffblue Limited

\*******************************************************************/

#include "interval_union.h"
#include "arith_tools.h"
#include "range.h"
#include "string_utils.h"
#include <regex>
#include <util/invariant.h>
#include <util/std_expr.h>

interval_uniont interval_uniont::all_integers()
{
  return of_interval(intervalt{});
}

interval_uniont interval_uniont::greater_or_equal(const mp_integer &value)
{
  interval_uniont interval_union{};
  intervalt interval;
  interval.make_ge_than(value);
  interval_union.intervals.emplace_back(std::move(interval));
  return interval_union;
}

interval_uniont interval_uniont::smaller_or_equal(const mp_integer &value)
{
  interval_uniont interval_union{};
  intervalt interval;
  interval.make_le_than(value);
  interval_union.intervals.emplace_back(std::move(interval));
  return interval_union;
}

interval_uniont
interval_uniont::make_intersection(const interval_uniont &other) const
{
  interval_uniont result{};
  auto it1 = intervals.begin();
  auto it2 = other.intervals.begin();
  while(it1 != intervals.end() && it2 != other.intervals.end())
  {
    intervalt intersection = *it1;
    intersection.intersect_with(*it2);
    if(!intersection.empty())
      result.intervals.emplace_back(std::move(intersection));
    if(it1->upper < it2->upper)
      ++it1;
    else
      ++it2;
  }
  return result;
}

interval_uniont interval_uniont::make_union(const interval_uniont &other) const
{
  if(intervals.empty())
    return other;
  if(other.intervals.empty())
    return *this;

  // The algorithm goes process the intervals contained in both unions in order
  // of their lower bound. At each iteration of the loop, the \c result object
  // contains the union of intervals from both sets that have lower bound
  // smaller than the intervals currently pointed by \c it1 and \c it2.
  interval_uniont result{};
  auto it1 = intervals.begin();
  auto it2 = other.intervals.begin();

  // Initialize the first interval of \c result depending on which of the two
  // sets are unbounded to the left.
  if(!it1->lower_set)
  {
    if(!it2->lower_set)
    {
      result = smaller_or_equal(std::max(it1->upper, it2->upper));
      ++it1;
      ++it2;
    }
    else
    {
      result.intervals.push_back(*it1);
      ++it1;
    }
  }
  else
  {
    if(!it2->lower_set)
    {
      result.intervals.push_back(*it2);
      ++it2;
    }
    else if(it1->lower <= it2->lower)
    {
      result.intervals.push_back(*it1);
      ++it1;
    }
    else
    {
      result.intervals.push_back(*it2);
      ++it2;
    }
  }
  while(it1 != intervals.end() || it2 != other.intervals.end())
  {
    intervalt &back = result.intervals.back();
    INVARIANT(
      !back.lower_set ||
        ((it1 == intervals.end() || it1->lower >= back.lower) &&
         (it2 == other.intervals.end() || it2->lower >= back.lower)),
      "intervals should be processed in order");
    INVARIANT(
      (it1 == intervals.end() || it1->lower_set) &&
        (it2 == other.intervals.end() || it2->lower_set),
      "intervals unbounded to the left should have been processed in prelude");
    if(it1 != intervals.end() && it1->lower <= back.upper + 1)
    {
      back.approx_union_with(*it1);
      ++it1;
    }
    else if(it2 != other.intervals.end() && it2->lower <= back.upper + 1)
    {
      back.approx_union_with(*it2);
      ++it2;
    }
    else if(
      it1 != intervals.end() &&
      (it2 == other.intervals.end() || it1->lower <= it2->lower))
    {
      result.intervals.push_back(*it1);
      ++it1;
    }
    else
    {
      result.intervals.push_back(*it2);
      ++it2;
    }
  }
  return result;
}

bool interval_uniont::is_empty() const
{
  return intervals.empty();
}

optionalt<mp_integer> interval_uniont::maximum() const
{
  if(intervals.empty())
    return {};
  const intervalt &back = intervals.back();
  if(back.upper_set)
    return back.upper;
  return {};
}

optionalt<mp_integer> interval_uniont::minimum() const
{
  if(intervals.empty())
    return {};
  const intervalt &front = intervals.front();
  if(front.lower_set)
    return front.lower;
  return {};
}

std::string interval_uniont::to_string() const
{
  if(intervals.empty())
    return "[]";
  std::ostringstream output;
  for(const intervalt &i : intervals)
  {
    output << '[';
    if(i.lower_set)
      output << i.lower;
    output << ':';
    if(i.upper_set)
      output << i.upper;
    output << "]";
  }
  return output.str();
}

exprt interval_uniont::make_contains_expr(const exprt &e) const
{
  return disjunction(make_range(intervals).map([&e](const intervalt &interval) {
    std::vector<exprt> conjuncts;
    if(interval.lower_set)
    {
      conjuncts.emplace_back(binary_relation_exprt{
        e, ID_ge, from_integer(interval.lower, e.type())});
    }
    if(interval.upper_set)
    {
      conjuncts.emplace_back(binary_relation_exprt{
        e, ID_le, from_integer(interval.upper, e.type())});
    }
    return conjunction(conjuncts);
  }));
}

interval_uniont
interval_uniont::of_interval(interval_uniont::intervalt interval)
{
  interval_uniont result;
  result.intervals.emplace_back(std::move(interval));
  return result;
}

optionalt<interval_uniont>
interval_uniont::of_string(const std::string &to_parse)
{
  const std::regex limits_regex("\\[(-\\d+|\\d*):(-\\d+|\\d*)\\]");
  interval_uniont result;
  for(const std::string &interval_string : split_string(to_parse, ','))
  {
    std::smatch base_match;
    if(!std::regex_match(interval_string, base_match, limits_regex))
      return {};
    intervalt interval;
    if(!base_match[1].str().empty())
      interval.make_ge_than(string2integer(base_match[1].str()));
    if(!base_match[2].str().empty())
      interval.make_le_than(string2integer(base_match[2].str()));
    if(!interval.empty())
      result = result.make_union(of_interval(interval));
  }
  INVARIANT(result.validate(), "intervals should be strictly ordered");
  return result;
}

optionalt<mp_integer> interval_uniont::as_singleton() const
{
  if(intervals.size() != 1)
    return {};
  const intervalt &interval = intervals[0];
  if(!interval.lower_set || !interval.upper_set)
    return {};
  if(interval.upper != interval.lower)
    return {};
  return interval.lower;
}

/// Check that interval \p a is strictly below interval \p b
static bool strictly_below(
  const interval_templatet<mp_integer> &a,
  const interval_templatet<mp_integer> &b)
{
  return a.upper_set && b.lower_set && a.upper < b.lower;
}

bool interval_uniont::validate() const
{
  return std::is_sorted(intervals.begin(), intervals.end(), strictly_below);
}
