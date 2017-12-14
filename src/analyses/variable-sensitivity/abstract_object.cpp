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
  return abstract_object_merge(other);
}

/*******************************************************************\

Function: abstract_objectt::abstract_object_merge

  Inputs:
   other - The object to merge with this

 Outputs: Returns the result of the abstract object.

 Purpose: Create a new abstract object that is the result of the merge, unless
          the object would be unchanged, then would return itself.

\*******************************************************************/

abstract_object_pointert abstract_objectt::abstract_object_merge(
  const abstract_object_pointert other) const
{
  if(top)
    return shared_from_this();
  if(other->bottom)
    return shared_from_this();


  internal_abstract_object_pointert merged=mutable_clone();
  merged->top=true;
  merged->bottom=false;
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
      // do not give up if a sub-expression is not a constant,
      // because the whole expression may still be simplified in some cases
      constant_replaced_expr.operands().push_back(op);
    }
    else
    {
      // rebuild the operands list with constant versions of
      // any symbols
      constant_replaced_expr.operands().push_back(lhs_value);
    }
  }

  exprt simplified=simplify_expr(constant_replaced_expr, ns);
  if(simplified.is_constant())
  {
    return environment.abstract_object_factory(
            simplified.type(), simplified, ns);
  }
  else
  {
    // if our final expression isn't a constant, just return top
    return environment.abstract_object_factory(expr.type(), ns, true, false);
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
  abstract_object_pointert result=op1->should_use_base_merge(op2)?
    op1->abstract_object_merge(op2):op1->merge(op2);
  // If no modifications, we will return the original pointer
  out_modifications=result!=op1;

  locationst get_location_union = op1->get_location_union(
      op2->get_last_written_locations());
  // If the union is larger than the initial set, then update.
  if(get_location_union.size() > op1->get_last_written_locations().size())
  {
    out_modifications=true;
    result=result->update_last_written_locations(get_location_union, false);
  }

  return result;
}

/*******************************************************************\

Function: abstract_objectt::should_use_base_merge

  Inputs:
   other - the object being merged with

 Outputs: Returns true if the base class is capable of doing a complete merge

 Purpose: To detect the cases where the base merge is sufficient to do a merge
          We can't do if this->is_bottom() since we want the specific

\*******************************************************************/

bool abstract_objectt::should_use_base_merge(
  const abstract_object_pointert other) const
{
  return is_top() || other->is_bottom() || other->is_top();
}

/*******************************************************************\

Function: abstract_objectt::update_last_written_locations

  Inputs:
   Set of locations to be written.

 Outputs:
   An abstract_object_pointer pointing to the cloned, updated object.

 Purpose: Creates a mutable clone of the current object, and updates
          the last written location map with the provided location(s).

          For immutable objects.

\*******************************************************************/

abstract_object_pointert abstract_objectt::update_last_written_locations(
    const locationst &locations,
    bool update_sub_elements) const
{
  internal_abstract_object_pointert clone=mutable_clone();
  clone->set_last_written_locations(locations);
  if(update_sub_elements)
    clone->update_sub_elements(locations);
  return clone;
}

/*******************************************************************\

Function: abstract_objectt::get_location_union

  Inputs:
   Set of locations unioned

 Outputs:
   The union of the two sets

 Purpose: Takes the location set of the current object, and unions it
          with the provided set.

\*******************************************************************/

abstract_objectt::locationst abstract_objectt::get_location_union(const locationst &locations) const
{
  locationst existing_locations=get_last_written_locations();
  existing_locations.insert(locations.begin(), locations.end());

  return existing_locations;
}

/*******************************************************************\

Function: abstract_objectt::set_last_written_locations

  Inputs:
   Set of locations to be written

 Outputs:
   Void

 Purpose: Writes the provided set to the object.

          For mutable objects.

\*******************************************************************/

void abstract_objectt::set_last_written_locations(const locationst &locations)
{
  last_written_locations=locations;
}

/*******************************************************************\

Function: abstract_objectt::get_last_written_locations

  Inputs:
   None

 Outputs:
   Set of locations for the provided object.

 Purpose: Getter for last_written_locations

\*******************************************************************/

abstract_objectt::locationst abstract_objectt::get_last_written_locations() const
{
  return last_written_locations;
}

/*******************************************************************\

Function: abstract_objectt::output_last_written_location

  Inputs:
   object - the object to read information from
   out - the stream to write to
   ai - the abstract interpreter that contains this domain
   ns - the current namespace

 Outputs: None

 Purpose: Print out all last written locations for a specified
          object

\*******************************************************************/

void abstract_objectt::output_last_written_locations(
  std::ostream &out,
  const abstract_objectt::locationst &locations)
{
  out << "[";
  bool comma=false;

  std::set<unsigned> sorted_locations;
  for(auto location: locations)
  {
    sorted_locations.insert(location->location_number);
  }

  for (auto location_number: sorted_locations)
  {
    if(!comma)
    {
      out << location_number;
      comma=true;
    }
    else
    {
      out << ", " << location_number;
    }
  }
  out << "]";
}

