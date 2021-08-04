/*******************************************************************\

 Module: Abstract interpretation for strict and monotonic change

 Authors: Long Pham, Saswat Padhi

\*******************************************************************/

// For the documentation of the class monotonic_changet, have a look at
// the header file monotonic_change.h.

#include <langapi/language_util.h>

#include <util/interval.h>
#include <util/std_expr.h>

#include "abstract_object_statistics.h"
#include "monotonic_change.h"

monotonic_changet::monotonic_changet(const typet &t)
  : abstract_value_objectt(t, false, false), monotonicity_value(unchanged)
{
}

monotonic_changet::monotonic_changet(const typet &t, bool tp, bool bttm)
  : abstract_value_objectt(t, tp, bttm),
    monotonicity_value((tp || bttm) ? top_or_bottom : unchanged)
{
}

monotonic_changet::monotonic_changet(
  const typet &t,
  bool tp,
  bool bttm,
  monotonicity_flags initial_value)
  : abstract_value_objectt(t, tp, bttm),
    monotonicity_value((tp || bttm) ? top_or_bottom : initial_value)
{
}

monotonic_changet::monotonic_changet(
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_value_objectt(e.type(), false, false), monotonicity_value(unchanged)
{
}

index_range_implementation_ptrt
monotonic_changet::index_range_implementation(const namespacet &ns) const
{
  return make_empty_index_range();
}

value_range_implementation_ptrt
monotonic_changet::value_range_implementation() const
{
  return make_single_value_range(shared_from_this());
}

constant_interval_exprt monotonic_changet::to_interval() const
{
  return constant_interval_exprt(type());
}

void monotonic_changet::set_top_internal()
{
  monotonicity_value = top_or_bottom;
}

void monotonic_changet::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  if(is_top() || is_bottom())
    abstract_objectt::output(out, ai, ns);
  else
  {
    switch(monotonicity_value)
    {
    case strict_increase:
      out << "Strictly and monotonically increasing";
      break;
    case strict_decrease:
      out << "Strictly and monotonically decreasing";
      break;
    case unchanged:
      out << "Staying unchanged";
      break;
    case top_or_bottom:
      // fall through
    default:
      UNREACHABLE;
    }
  }
}

abstract_object_pointert monotonic_changet::merge_with_value(
  const abstract_value_pointert &other,
  const widen_modet &widen_mode) const
{
  auto other_monotonic_change =
    std::dynamic_pointer_cast<const monotonic_changet>(other);
  if(other_monotonic_change != nullptr)
    return merge_with_monotonic_change(other_monotonic_change);
  else
    return abstract_objectt::merge(other, widen_mode);
}


/*
The result of merging two abstract states is given by the join (i.e. least upper
bound) of this lattice:
              top
           /   |   \
          /    |    \
         /     |     \
        /      |      \
increase   unchanged  decrease
       \       |      /
        \      |     /
         \     |    /
           \   |   /
            bottom
*/
abstract_object_pointert monotonic_changet::merge_with_monotonic_change(
  const sharing_ptrt<const monotonic_changet> &other) const
{
  if(this->is_bottom() || other->is_top())
    return std::make_shared<const monotonic_changet>(*other);
  if(this->is_top() || other->is_bottom())
    return shared_from_this();

  if(this->monotonicity_value == strict_increase)
  {
    switch(other->monotonicity_value)
    {
    case strict_increase:
      // If the result of merge is semantically the same as the current abstract
      // value, then we should return shared_from_this(), instead of a distinct
      // copy of the same abstract value. This is because, in the function
      // abstract_objectt::merge, to check whether merging changes the abstract
      // value, we compare pointers rather than the contents of abstract
      // objects. This is important for widening in fixed-point computation in
      // abstract interpretation. If we inadvertently returned a new copy of the
      // same abstract value, the widening for loops would diverge (i.e.
      // non-termination).
      return shared_from_this();
    case unchanged:
      // fall through
    case strict_decrease:
      return std::make_shared<monotonic_changet>(
        this->type(), true, false); // top
    case top_or_bottom:
      // fall through
    default:
      UNREACHABLE;
    }
  }
  else if(this->monotonicity_value == strict_decrease)
  {
    switch(other->monotonicity_value)
    {
    case strict_increase:
      // fall through
    case unchanged:
      return std::make_shared<monotonic_changet>(
        this->type(), true, false); // top
    case strict_decrease:
      return shared_from_this();
    case top_or_bottom:
      // fall through
    default:
      UNREACHABLE;
    }
  }
  else if(this->monotonicity_value == unchanged)
  {
    switch(other->monotonicity_value)
    {
    case strict_increase:
      return std::make_shared<monotonic_changet>(
        this->type(), true, false); // top
    case unchanged:
      return shared_from_this();
    case strict_decrease:
      return std::make_shared<monotonic_changet>(
        this->type(), true, false); // top
    case top_or_bottom:
      // fall through
    default:
      UNREACHABLE;
    }
  }
  else // this->monotonicity_value == top_or_bottom
    UNREACHABLE;

  // We return the top by default.
  return std::make_shared<monotonic_changet>(this->type(), true, false);
}

abstract_object_pointert
monotonic_changet::meet_with_value(const abstract_value_pointert &other) const
{
  auto other_monotonic_change =
    std::dynamic_pointer_cast<const monotonic_changet>(other);
  if(other_monotonic_change != nullptr)
    return meet_with_monotonic_change(other_monotonic_change);
  else
    return abstract_objectt::meet(other);
}

abstract_object_pointert monotonic_changet::meet_with_monotonic_change(
  const sharing_ptrt<const monotonic_changet> &other) const
{
  if(this->is_bottom() || other->is_top())
    return shared_from_this();
  if(this->is_top() || other->is_bottom())
    return std::make_shared<monotonic_changet>(*other);

  if(this->monotonicity_value == strict_increase)
  {
    switch(other->monotonicity_value)
    {
    case strict_increase:
      return shared_from_this();
    case unchanged:
      // fall through
    case strict_decrease:
      return std::make_shared<monotonic_changet>(
        this->type(), false, true); // bottom
    case top_or_bottom:
      // fall through
    default:
      UNREACHABLE;
    }
  }
  else if(this->monotonicity_value == unchanged)
  {
    switch(other->monotonicity_value)
    {
    case strict_increase:
      return std::make_shared<monotonic_changet>(
        this->type(), false, true); // bottom
    case unchanged:
      return shared_from_this();
    case strict_decrease:
      return std::make_shared<monotonic_changet>(
        this->type(), false, true); // bottom
    case top_or_bottom:
      // fall through
    default:
      UNREACHABLE;
    }
  }
  else if(this->monotonicity_value == strict_decrease)
  {
    switch(other->monotonicity_value)
    {
    case strict_increase:
      // fall through
    case unchanged:
      return std::make_shared<monotonic_changet>(
        this->type(), false, true);
    case strict_decrease:
      return shared_from_this();
    case top_or_bottom:
      // fall through
    default:
      UNREACHABLE;
    }
  }
  else
    UNREACHABLE;

  // We return the bottom by default.
  return std::make_shared<monotonic_changet>(this->type(), false, true);
}

abstract_value_pointert
monotonic_changet::constrain(const exprt &lower, const exprt &upper) const
{
  return as_value(mutable_clone());
}

void monotonic_changet::get_statistics(
  abstract_object_statisticst &statistics,
  abstract_object_visitedt &visited,
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  abstract_objectt::get_statistics(statistics, visited, env, ns);
  statistics.objects_memory_usage += memory_sizet::from_bytes(sizeof(*this));
}
