/*******************************************************************\

 Module: Predicate abstraction for monotonic change

 Authors: Long Pham, Saswat Padhi

\*******************************************************************/

// For the documentation of the class monotonic_changet, have a look at
// the header file monotonic_change.h.

#include <langapi/language_util.h>

#include <util/interval.h>
#include <util/std_expr.h>

#include "abstract_object_statistics.h"
#include "monotonic_change.h"

// We will print out a message on the standard output when we encouter a
// pathological case. An example is when we are try to merge the abstract value
// "uninitialized" with other abstract values (e.g. "increase"). This is why we
// need <iostream>.
#include <iostream>

monotonic_changet::monotonic_changet(const typet &t)
  : abstract_value_objectt(t, false, false), monotonicity_value(uninitialized)
{
}

monotonic_changet::monotonic_changet(const typet &t, bool tp, bool bttm)
  : abstract_value_objectt(t, tp, bttm),
    monotonicity_value((tp || bttm) ? top_or_bottom : uninitialized)
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
  : abstract_value_objectt(e.type(), false, false), monotonicity_value(constant)
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
    case increase:
      out << "Monotonically increasing";
      break;
    case decrease:
      out << "Monotonically decreasing";
      break;
    case constant:
      out << "Staying constant";
      break;
    case uninitialized:
      out << "Declared but uninitialized";
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

// It is weird if we ever try to merge uninitialized with increase, constant, or
// decrease. In such a pathological case, we print out a message on the standard
// output and simply return the top.
abstract_object_pointert monotonic_changet::merge_with_monotonic_change(
  const sharing_ptrt<const monotonic_changet> &other) const
{
  if(this->is_bottom() || other->is_top())
    return std::make_shared<const monotonic_changet>(*other);
  if(this->is_top() || other->is_bottom())
    return shared_from_this();

  if(this->monotonicity_value == increase)
  {
    switch(other->monotonicity_value)
    {
    case increase:
      // fall through
    case constant:
      // If the result of merge is semantically the same as the current abstract
      // value, then we should return shared_from_this(), instead of a new copy
      // with the same abstract value. This is because, in the function
      // abstract_objectt::merge, to checks whether merging changes the abstract
      // value, we compare pointers rather than the contents of abstract
      // objects. This is important for widening for loops in abstract
      // interpretation. If we inadvertently returned a new copy of the same
      // abstract value, the widening for loops would diverge (i.e.
      // non-termination).
      return shared_from_this();
    case decrease:
      return std::make_shared<monotonic_changet>(
        this->type(), true, false); // top
    case uninitialized:
      std::cout << "We are trying to merge increase with uninitialized\n";
      break;
    case top_or_bottom:
      // fall through
    default:
      UNREACHABLE;
    }
  }
  else if(this->monotonicity_value == decrease)
  {
    switch(other->monotonicity_value)
    {
    case increase:
      return std::make_shared<monotonic_changet>(
        this->type(), true, false); // top
    case constant:
      // fall through
    case decrease:
      return shared_from_this();
    case uninitialized:
      std::cout << "We are trying to merge decrease with uninitialized\n";
      break;
    case top_or_bottom:
      // fall through
    default:
      UNREACHABLE;
    }
  }
  else if(this->monotonicity_value == constant)
  {
    switch(other->monotonicity_value)
    {
    case increase:
      return std::make_shared<monotonic_changet>(
        this->type(), false, false, increase);
    case constant:
      return shared_from_this();
    case decrease:
      return std::make_shared<monotonic_changet>(
        this->type(), false, false, decrease);
    case uninitialized:
      std::cout << "We are trying to merge constant with uninitialized\n";
      break;
    case top_or_bottom:
      // fall through
    default:
      UNREACHABLE;
    }
  }
  else if(this->monotonicity_value == uninitialized)
  {
    switch(other->monotonicity_value)
    {
    case increase:
      // fall through
    case constant:
      // fall through
    case decrease:
      std::cout << "We are trying to merge uninitialized with increase, "
                   "constant, or decrease\n";
      break;
    case uninitialized:
      return shared_from_this();
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

  std::shared_ptr<monotonic_changet> result_pointer =
    std::make_shared<monotonic_changet>(
      this->type(), false, false, uninitialized);

  if(this->monotonicity_value == increase)
  {
    switch(other->monotonicity_value)
    {
    case increase:
      return std::make_shared<monotonic_changet>(
        this->type(), false, false, increase);
    case constant:
      // fall through
    case decrease:
      return std::make_shared<monotonic_changet>(
        this->type(), false, false, constant);
    case uninitialized:
      std::cout << "Meet of increase and uninitialized\n";
      break;
    case top_or_bottom:
      // fall through
    default:
      UNREACHABLE;
    }
  }
  else if(this->monotonicity_value == constant)
  {
    switch(other->monotonicity_value)
    {
    case increase:
      // fall through
    case constant:
      // fall through
    case decrease:
      return std::make_shared<monotonic_changet>(
        this->type(), false, false, constant);
    case uninitialized:
      std::cout << "Meet of constant and uninitialized\n";
      break;
    case top_or_bottom:
      // fall through
    default:
      UNREACHABLE;
    }
  }
  else if(this->monotonicity_value == decrease)
  {
    switch(other->monotonicity_value)
    {
    case increase:
      // fall through
    case constant:
      return std::make_shared<monotonic_changet>(
        this->type(), false, false, constant);
    case decrease:
      return std::make_shared<monotonic_changet>(
        this->type(), false, false, decrease);
    case uninitialized:
      std::cout << "Meet of decrease and uninitialized\n";
      break;
    case top_or_bottom:
      // fall through
    default:
      UNREACHABLE;
    }
  }
  else if(this->monotonicity_value == uninitialized)
  {
    switch(other->monotonicity_value)
    {
    case increase:
      // fall through
    case constant:
      // fall through
    case decrease:
      std::cout
        << "Meet of uninitialized with increase, constant, or decrease\n";
      break;
    case uninitialized:
      return std::make_shared<monotonic_changet>(
        this->type(), false, false, uninitialized);
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
