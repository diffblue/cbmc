/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <iostream>

#include <util/type.h>
#include <util/std_expr.h>
#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>

#include <util/simplify_expr.h>
#include <util/namespace.h>

#include "abstract_object.h"

/*******************************************************************\

Function: abstract_objectt::abstract_objectt

  Inputs:
   type - the type the abstract_object is representing

 Outputs:

 Purpose:

\*******************************************************************/

abstract_objectt::abstract_objectt(const typet &type):
type(type), top(true), bottom(false)
{}

/*******************************************************************\

Function: abstract_objectt::abstract_objectt

  Inputs:
   type - the type the abstract_object is representing
   top - is the abstract_object starting as top
   bottom - is the abstract_object starting as bottom

 Outputs:

 Purpose: Start the abstract object at either top or bottom or neither
          Asserts if both top and bottom are true

\*******************************************************************/

abstract_objectt::abstract_objectt(const typet &type, bool top, bool bottom):
  type(type), top(top), bottom(bottom)
{
  assert(!(top && bottom));
}

/*******************************************************************\

Function: abstract_objectt::abstract_objectt

  Inputs:
   old - the abstract object to copy from

 Outputs:

 Purpose:

\*******************************************************************/

abstract_objectt::abstract_objectt(const abstract_objectt &old):
  type(old.type), top(old.top), bottom(old.bottom)
{}

/*******************************************************************\

Function: abstract_objectt::abstract_objectt

  Inputs:
   expr - the expression to use as the starting pointer for an abstract object

 Outputs:

 Purpose:

\*******************************************************************/

abstract_objectt::abstract_objectt(const constant_exprt &expr):
type(expr.type()), top(true), bottom(false)
{}

const typet &abstract_objectt::get_type() const
{
  return type;
}

/*******************************************************************\

Function: abstract_objectt::merge_state

  Inputs:
   op1 - the first abstract object
   op2 - the second abstract object

 Outputs:

 Purpose: Set this abstract object to be the result of merging two
          other abstract objects. This is the worst case - we can
          only set to top or bottom.

\*******************************************************************/

bool abstract_objectt::merge_state(
  const abstract_object_pointert op1, const abstract_object_pointert op2)
{
  top=op1->top||op2->top;
  bottom=op1->bottom && op2->bottom;

  assert(!(top && bottom));
  return top!=op1->top || bottom!=op1->bottom;
}

/*******************************************************************\

Function: abstract_objectt::merge

  Inputs:
   op - the abstract object to merge with

 Outputs:

 Purpose: Set this abstract object to be the result of merging this
          abstract object and the provided one. See merge_state.

\*******************************************************************/

abstract_object_pointert abstract_objectt::merge(
  const abstract_object_pointert op, bool &out_any_modifications)
{
  assert(type==op->type);
  abstract_object_pointert m=abstract_object_pointert(new abstract_objectt(*this));
  out_any_modifications=m->merge_state(abstract_object_pointert(this), op);
  return m;
}

abstract_object_pointert abstract_objectt::expression_transform_binary(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  assert(expr.operands().size()==2);

  abstract_object_pointert lhs_abstract_object=environment.eval(expr.op0(), ns);
  abstract_object_pointert rhs_abstract_object=environment.eval(expr.op1(), ns);

  const exprt &lhs_value=lhs_abstract_object->to_constant();
  const exprt &rhs_value=rhs_abstract_object->to_constant();

  if(lhs_value.id()==ID_nil || rhs_value.id()==ID_nil)
  {
    // One or both of the values is unknown so therefore we can't conclude
    // whether this is true or false
    return abstract_object_pointert(
      new abstract_objectt(expr.type(), true, false));
  }
  else
  {
    exprt constant_replaced_expr=expr;
    constant_replaced_expr.operands()[0]=lhs_value;
    constant_replaced_expr.operands()[1]=rhs_value;
    exprt simplified=simplify_expr(constant_replaced_expr, ns);
    if(simplified.is_constant())
    {
      constant_exprt constant_expr=to_constant_expr(simplified);

      // TODO(tkiley): This should be going through the abstract_object_factory
      // but at the moment this produces a two value abstraction for type bool
      // so for now we force it to be the constant abstraction
      return abstract_object_pointert(
        new constant_abstract_valuet(constant_expr));
    }
    else
    {
      return environment.abstract_object_factory(expr.type(), true, false);
    }
  }
}

/*******************************************************************\

Function: abstract_objectt::is_top

  Inputs:

 Outputs: Returns true if the abstract object is representing the top (i.e. we
          don't know anything about the value).

 Purpose: Find out if the abstract object is top

\*******************************************************************/

bool abstract_objectt::is_top() const
{
  return top;
}

/*******************************************************************\

Function: abstract_objectt::is_bottom

  Inputs:

 Outputs: Returns true if the abstract object is representing the bottom.

 Purpose: Find out if the abstract object is bottom

\*******************************************************************/

bool abstract_objectt::is_bottom() const
{
  return bottom;
}

/*******************************************************************\

Function: abstract_objectt::to_constant

  Inputs:

 Outputs: Returns an exprt representing the value if the value is known and
          constant. Otherwise returns the nil expression

 Purpose: If abstract element represents a single value, then that value,
          otherwise nil. E.G. if it is an interval then this will be x if it is
          [x,x] This is the (sort of) dual to the constant_exprt constructor
          that allows an object to be built from a value.

\*******************************************************************/

exprt abstract_objectt::to_constant() const
{
  return nil_exprt();
}

/*******************************************************************\

Function: abstract_objectt::output

  Inputs:
   out - the stream to write to
   ai - ?
   ns - ?

 Outputs:

 Purpose: Print the value of the abstract object

\*******************************************************************/

void abstract_objectt::output(
  std::ostream &out, const ai_baset &ai, const namespacet &ns)
{
  if(top)
  {
    out << "TOP";
  }
  else if(bottom)
  {
    out << "BOTTOM";
  }
  else
  {
    out << "Unknown";
  }
}
