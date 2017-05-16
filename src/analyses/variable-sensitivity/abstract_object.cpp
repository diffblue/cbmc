/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <iostream>

#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>

#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/simplify_expr.h>
#include <util/type.h>

#include "abstract_object.h"

/*******************************************************************\

Function: abstract_objectt::abstract_objectt

  Inputs:
   type - the type the abstract_object is representing

 Outputs:

 Purpose:

\*******************************************************************/

abstract_objectt::abstract_objectt(const typet &type):
t(type), bottom(false), top(true)
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
  t(type), bottom(bottom), top(top)
{
  assert(!(top && bottom));
}

/*******************************************************************\

Function: abstract_objectt::abstract_objectt

  Inputs:
   expr - the expression to use as the starting pointer for an abstract object
   environment - The environment this abstract object is being created in
   ns - the namespace

 Outputs:

 Purpose: Construct an abstract object from the expression

\*******************************************************************/

abstract_objectt::abstract_objectt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns):
    t(expr.type()), bottom(false), top(true)
{}

/*******************************************************************\

Function: abstract_objectt::type

  Inputs:

 Outputs: The program type this abstract object represents

 Purpose: Get the real type of the variable this abstract object is
          representing.

\*******************************************************************/
const typet &abstract_objectt::type() const
{
  return t;
}

/*******************************************************************\

Function: abstract_objectt::merge

  Inputs:
   other - The object to merge with this

 Outputs: Returns the result of the merge.

 Purpose: Create a new abstract object that is the result of the merge, unless
          the object would be unchanged, then would return itself.

\*******************************************************************/

abstract_object_pointert abstract_objectt::merge(
  abstract_object_pointert other) const
{
  if(top)
    return shared_from_this();
  if(other->bottom)
    return shared_from_this();

  internal_abstract_object_pointert merged=mutable_clone();

  // We are top if and only if the other is top (since this is not)
  merged->top=other->top;

  // Other is definitely not bottom, so the merge definitely can't be bottom
  merged->bottom=false;

  assert(!(merged->top && merged->bottom));
  return merged;
}


/*******************************************************************\

Function: abstract_objectt::expression_transform

  Inputs:
   expr - the expression to evaluate and find the result of it. this will
          be the symbol referred to be op0()

 Outputs: Returns the abstract_object representing the result of this expression
          to the maximum precision available.

 Purpose: To try and resolve different expressions with the maximum level
          of precision available.

\*******************************************************************/

abstract_object_pointert abstract_objectt::expression_transform(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  exprt constant_replaced_expr=expr;
  constant_replaced_expr.operands().clear();
  for(const exprt &op : expr.operands())
  {
    abstract_object_pointert lhs_abstract_object=environment.eval(op, ns);
    const exprt &lhs_value=lhs_abstract_object->to_constant();

    if(lhs_value.is_nil())
    {
      // One of the values is not resolvable to a constant
      // so we can't really do anything more with
      // this expression and should just return top for the result
      return environment.abstract_object_factory(expr.type(), ns, true, false);
    }
    else
    {
      // rebuild the operands list with constant versions of
      // any symbols
      constant_replaced_expr.operands().push_back(lhs_value);
    }
  }

  exprt simplified=simplify_expr(constant_replaced_expr, ns);
  return environment.abstract_object_factory(simplified.type(), simplified, ns);
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
   ai - the abstract interpreter that contains the abstract domain
        (that contains the object ... )
   ns - the current namespace

 Outputs:

 Purpose: Print the value of the abstract object

\*******************************************************************/

void abstract_objectt::output(
  std::ostream &out, const ai_baset &ai, const namespacet &ns) const
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

/*******************************************************************\

Function: abstract_objectt::merge

  Inputs:
   op1 - the first abstract object to merge, this object determines
         the sensitivity of the output and is the object compared against
         to choose whether this merge changed anything
   op2 - the second abstract object to merge

 Outputs: The merged abstract object with the same sensitivity as the
          first parameter. out_modifications will be true if the resulting
          abstract object is different from op1

 Purpose: Clones the first parameter and merges it with the second.


\*******************************************************************/

abstract_object_pointert abstract_objectt::merge(
  abstract_object_pointert op1,
  abstract_object_pointert op2,
  bool &out_modifications)
{
  abstract_object_pointert result=op1->merge(op2);
  // If no modifications, we will return the original pointer
  out_modifications=result!=op1;
  return result;
}


