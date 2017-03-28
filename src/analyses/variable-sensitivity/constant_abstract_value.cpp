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
  const constant_abstract_valuet &old):
    abstract_valuet(old), value(old.value)
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

bool constant_abstract_valuet::merge_state(
  constant_abstract_value_pointert op1,
  constant_abstract_value_pointert op2)
{
  bool parent_merge_change=abstract_objectt::merge_state(op1, op2);
  if(!is_top() && !is_bottom())
  {
    if(op1->value==op2->value)
    {
      value=op1->value;
      return false;
    }
    else // values different
    {
      make_top();
      assert(is_bottom()==false);
      // Clear out the expression
      value=exprt();
      return !op1->is_top();
    }
  }
  else // either top or bottom
  {
    return parent_merge_change;
  }
}
