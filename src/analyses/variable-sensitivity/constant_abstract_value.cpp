/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#include "constant_abstract_value.h"

#include <util/std_expr.h>

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

constant_abstract_valuet::constant_abstract_valuet(const constant_exprt e):
  abstract_valuet(e), value(e)
{
  top=false;
}

exprt constant_abstract_valuet::to_constant() const
{
  if(!top && !bottom)
  {
    return this->value;
  }
  else
  {
    return abstract_objectt::to_constant();
  }
}

bool constant_abstract_valuet::operator==(const abstract_objectt &other) const
{
  // We can cast since should only be using == on same abstract object
  const constant_abstract_valuet &other_consant_value=
    dynamic_cast<const constant_abstract_valuet&>(other);

  return abstract_valuet::operator==(other) && value==other_consant_value.value;
}

void constant_abstract_valuet::output(
  std::ostream &out, const ai_baset &ai, const namespacet &ns)
{
  if(!top && !bottom)
  {
    out << to_constant_expr(value).get_value();
  }
  else
  {
    abstract_objectt::output(out, ai, ns);
  }
}

void constant_abstract_valuet::merge_state(
constant_abstract_value_pointert op1,
constant_abstract_value_pointert op2)
{
  abstract_objectt::merge_state(op1, op2);
  if (!top && !bottom)
  {
    if (op1->value==op2->value)
      value=op1->value;
    else
    {
      top=true;
      assert(bottom==false);
      // Clear out the expression
      value=exprt();
    }
  }
}
