/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <ostream>

#include <util/invariant.h>
#include <util/std_expr.h>

#include "abstract_enviroment.h"

#include "interval_abstract_value.h"

interval_abstract_valuet::interval_abstract_valuet(typet t):
  abstract_valuet(t), interval()
{}

interval_abstract_valuet::interval_abstract_valuet(typet t, bool tp, bool bttm):
  abstract_valuet(t, tp, bttm), interval()
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

/*******************************************************************\

Function: interval_abstract_valuet::merge

  Inputs:
   other - the abstract object to merge with

 Outputs: Returns the result of the merge

 Purpose: Attempts to do a interval/interval merge if both are intervals,
          otherwise falls back to the parent merge


\*******************************************************************/

abstract_object_pointert interval_abstract_valuet::merge(
  abstract_object_pointert other) const
{
  interval_abstract_value_pointert cast_other=
    std::dynamic_pointer_cast<const interval_abstract_valuet>(other);
  if(cast_other)
  {
    return merge_interval_interval(cast_other);
  }
  else
  {
    // TODO(tkiley): How do we set the result to be toppish? Does it matter?
    return abstract_valuet::merge(other);
  }
}

/*******************************************************************\

Function: interval_abstract_valuet::merge_interval_interval

  Inputs:
   other - the abstract object to merge with

 Outputs: Returns a new abstract object that is the result of the merge
          unless the merge is the same as this abstract object, in which
          case it returns this.

 Purpose: Merges another interval abstract value into this one

\*******************************************************************/

abstract_object_pointert interval_abstract_valuet::merge_interval_interval(
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

#if 0
    // Can we actually merge these value
    if(value==other->value)
    {
      return shared_from_this();
    }
    else
    {
      return abstract_valuet::merge(other);
    }
  }
#endif
}
