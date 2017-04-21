/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <ostream>

#include <util/std_expr.h>

#include "constant_abstract_value.h"

constant_abstract_valuet::constant_abstract_valuet(typet t):
  abstract_valuet(t), value()
{}

constant_abstract_valuet::constant_abstract_valuet(typet t, bool tp, bool bttm):
  abstract_valuet(t, tp, bttm), value()
{}

constant_abstract_valuet::constant_abstract_valuet(
  const exprt e,
  const abstract_environmentt &environment,
  const namespacet &ns):
    abstract_valuet(e.type(), false, false), value(e)
{}

exprt constant_abstract_valuet::to_constant() const
{
  if(!is_top() && !is_bottom())
  {
    return this->value;
  }
  else
  {
    return abstract_objectt::to_constant();
  }
}

void constant_abstract_valuet::output(
  std::ostream &out, const ai_baset &ai, const namespacet &ns) const
{
  if(!is_top() && !is_bottom())
  {
    out << to_constant_expr(value).get_value();
  }
  else
  {
    abstract_objectt::output(out, ai, ns);
  }
}

/*******************************************************************\

Function: constant_abstract_valuet::merge

  Inputs:
   other - the abstract object to merge with

 Outputs: Returns true if this changes when performing this merge

 Purpose: Attempts to do a constant/constant merge if both are constants,
          otherwise falls back to the parent merge


\*******************************************************************/

bool constant_abstract_valuet::merge(abstract_object_pointert other)
{
  constant_abstract_value_pointert cast_other=
    std::dynamic_pointer_cast<const constant_abstract_valuet>(other);
  if(cast_other)
  {
    return merge_constant_constant(cast_other);
  }
  else
  {
    value=exprt();
    return abstract_valuet::merge(other);
  }
}

/*******************************************************************\

Function: constant_abstract_valuet::merge_constant_constant

  Inputs:
   other - the abstract object to merge with

 Outputs: Returns true if this changes when performing this merge


 Purpose: Merges another constant abstract value into this one

\*******************************************************************/

bool constant_abstract_valuet::merge_constant_constant(
  constant_abstract_value_pointert other)
{
  bool was_top=is_top();
  bool parent_merge_change=abstract_valuet::merge(other);

  if(!is_top() && !is_bottom())
  {
    if(value==other->value)
    {
      return false;
    }
    else
    {
      make_top();
      assert(!is_bottom());
      value=exprt();
      return !was_top;
    }
  }
  else
  {
    return parent_merge_change;
  }
}
