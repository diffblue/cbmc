/*******************************************************************\

 Module: analyses variable-sensitivity intervals

 Author: Diffblue Ltd.

\*******************************************************************/

#include <ostream>

#include <util/invariant.h>
#include <util/std_expr.h>

#include "abstract_enviroment.h"

#include "interval_abstract_value.h"

static inline exprt look_through_casts(exprt e) {
  while(e.id() == ID_typecast) {
    e = e.op0();
  }
  return e;
}

static inline constant_interval_exprt make_interval_expr(exprt e) {
  e = look_through_casts(e);
  if(e.id() == ID_constant_interval) {
    return to_constant_interval_expr(e);
  } else if(e.id() == ID_constant) {
    return constant_interval_exprt(e, e);
  } else {
    // not directly representable, so just return TOP
    return constant_interval_exprt(e.type());
  }
}

interval_abstract_valuet::interval_abstract_valuet(typet t):
  abstract_valuet(t), interval(t)
{}

interval_abstract_valuet::interval_abstract_valuet(typet t, bool tp, bool bttm):
  abstract_valuet(t, tp, bttm), interval(t)
{}

interval_abstract_valuet::interval_abstract_valuet(
  const constant_interval_exprt e):
    abstract_valuet(e.type(), false, false), interval(e)
{

}

exprt interval_abstract_valuet::to_constant() const
{
  if(!is_top() && !is_bottom())
  {
    return this->interval;
  }
  else
  {
    return abstract_objectt::to_constant();
  }
}

#if 1
// Interface for transforms
abstract_object_pointert interval_abstract_valuet::expression_transform(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  if(expr.id() == ID_constant_interval)
  {
    return environment.abstract_object_factory(expr.type(), expr, ns);
  }
  else
  {
    return abstract_objectt::expression_transform(expr, environment, ns);
  }
}
#endif

void interval_abstract_valuet::output(
  std::ostream &out, const ai_baset &ai, const namespacet &ns) const
{
  if(!is_top() && !is_bottom())
  {
    std::string lower_string;
    std::string upper_string;

    if(interval.get_lower().id() == ID_min) {
      lower_string = "-INF";
    } else {
      INVARIANT(interval.get_lower().id() == ID_constant,
          "We only support constant limits");
      lower_string = id2string(to_constant_expr(interval.get_lower()).get_value());
    }

    if(interval.get_upper().id() == ID_max) {
      upper_string = "+INF";
    } else {
      INVARIANT(interval.get_lower().id() == ID_constant,
                "We only support constant limits");
      upper_string = id2string(to_constant_expr(interval.get_upper()).get_value());
    }

    out << "[" << lower_string << ", " << upper_string << "]";
  }
  else
  {
    abstract_objectt::output(out, ai, ns);
  }
}

abstract_object_pointert interval_abstract_valuet::merge(
  abstract_object_pointert other) const
{
  interval_abstract_value_pointert cast_other=
    std::dynamic_pointer_cast<const interval_abstract_valuet>(other);
  if(cast_other)
  {
    return merge_intervals(cast_other);
  }
  else
  {
    return abstract_valuet::merge(other);
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
    return std::make_shared<interval_abstract_valuet>(
      constant_interval_exprt(
        constant_interval_exprt::get_min(interval.get_lower(), other->interval.get_lower()),
        constant_interval_exprt::get_max(interval.get_upper(), other->interval.get_upper())));
  }
}

interval_abstract_valuet::interval_abstract_valuet(const exprt e, const abstract_environmentt &environment,
                                                   const namespacet &ns)
  : interval_abstract_valuet(make_interval_expr(e))
{}
