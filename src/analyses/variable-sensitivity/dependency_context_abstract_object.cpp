/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Chris Ryder, chris.ryder@diffblue.com

\*******************************************************************/

#include <util/std_types.h>
#include <ostream>
#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include "dependency_context_abstract_object.h"
#include "full_struct_abstract_object.h"

void dependency_context_abstract_objectt::set_child(
  const abstract_object_pointert &child)
{
  child_abstract_object = child;
}

void dependency_context_abstract_objectt::make_top_internal()
{
  if(!child_abstract_object->is_top())
    set_child(child_abstract_object->make_top());
}

void dependency_context_abstract_objectt::clear_top_internal()
{
  if(child_abstract_object->is_top())
    set_child(child_abstract_object->clear_top());
}

/*******************************************************************\

Function: dependency_context_abstract_objectt::update_last_written_locations

  Inputs:
   Set of locations to be written.

 Outputs:
   An abstract_object_pointer pointing to the cloned, updated object.

 Purpose: Creates a mutable clone of the current object, and updates
          the last written location map with the provided location(s).

          For immutable objects.

\*******************************************************************/
abstract_object_pointert
  dependency_context_abstract_objectt::update_last_written_locations(
    const abstract_objectt::locationst &locations,
    const bool update_sub_elements) const
{
  const auto &result=
    std::dynamic_pointer_cast<dependency_context_abstract_objectt>(
      mutable_clone());

  result->set_child(child_abstract_object->update_last_written_locations(
    locations, update_sub_elements));

  result->set_last_written_locations(locations);
  return result;
}

abstract_objectt::locationst
  dependency_context_abstract_objectt::get_last_written_locations() const
{
  return last_written_locations;
}

/**
 * A helper function to evaluate an abstract object contained
 * within a container object. More precise abstractions may override this
 * to return more precise results.
 *
 * \param env the abstract environment
 * \param specifier a modifier expression, such as an array index or field
 * specifier used to indicate access to a specific component
 * \param ns the current namespace
 *
 * \return the abstract_objectt representing the value of the read component.
 * For the dependency context, the operation is simply delegated to the
 * child object
 */
abstract_object_pointert dependency_context_abstract_objectt::read(
  const abstract_environmentt &env,
  const exprt &specifier,
  const namespacet &ns) const
{
  return child_abstract_object->read(env, specifier, ns);
}

/**
 * A helper function to evaluate writing to a component of an
 * abstract object. More precise abstractions may override this to
 * update what they are storing for a specific component.
 *
 * \param environment the abstract environment
 * \param ns the current namespace
 * \param stack the remaining stack of expressions on the LHS to evaluate
 * \param specifier the expression uses to access a specific component
 * \param value the value we are trying to write to the component
 * \param merging_write if true, this and all future writes will be merged
 * with the current value
 *
 * \return the abstract_objectt representing the result of writing
 * to a specific component.
 */
abstract_object_pointert dependency_context_abstract_objectt::write(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> stack,
  const exprt &specifier,
  const abstract_object_pointert value,
  bool merging_write) const
{
  // But delegate the write to the child
  abstract_object_pointert updated_child=
    child_abstract_object->write(
      environment, ns, stack, specifier, value, merging_write);

  // Only perform an update if the write to the child has in fact changed it...
  // FIXME: But do we still want to record the write???
  if(updated_child == child_abstract_object)
    return shared_from_this();

  // Need to ensure the result of the write is still wrapped in a dependency
  // context
  const auto &result=
    std::dynamic_pointer_cast<dependency_context_abstract_objectt>(
      mutable_clone());

  // Update the child and record the updated write locations
  result->set_child(updated_child);
  result->set_last_written_locations(value->get_last_written_locations());

  return result;
}

/**
 * Create a new abstract object that is the result of merging this abstract
 * object with a given abstract_object
 *
 * \param other the abstract object to merge with
 *
 * \return the result of the merge, or 'this' if the merge would not change
 * the current abstract object
 */
abstract_object_pointert dependency_context_abstract_objectt::merge(
  abstract_object_pointert other) const
{
  auto cast_other=
    std::dynamic_pointer_cast<const dependency_context_abstract_objectt>(other);

  if(cast_other)
  {
    bool child_modified=false;

    auto merged_child=
      abstract_objectt::merge(
        child_abstract_object, cast_other->child_abstract_object,
        child_modified);

    abstract_objectt::locationst location_union=get_location_union(
      cast_other->get_last_written_locations());
    // If the union is larger than the initial set, then update.
    bool merge_locations =
      location_union.size()>get_last_written_locations().size();

    if(child_modified || merge_locations)
    {
      const auto &result=
        std::dynamic_pointer_cast<dependency_context_abstract_objectt>(
          mutable_clone());
      if(child_modified)
      {
        result->set_child(merged_child);
      }
      if(merge_locations)
      {
        result->set_last_written_locations(location_union);
      }

      return result;
    }

    return shared_from_this();
  }

  return abstract_objectt::merge(other);
}

/**
 * Helper function for abstract_objectt::abstract_object_merge to perform any
 * additional actions after the base abstract_object_merge has completed it's
 * actions but immediately prior to it returning. As such, this function gives
 * the ability to perform additional work for a merge.
 *
 * For the dependency context, this additional work is the tracking of
 * last_written_locations across the merge
 *
 * \param other the object to merge with this
 *
 * \return the result of the merge
 */
abstract_object_pointert
  dependency_context_abstract_objectt::abstract_object_merge_internal(
    const abstract_object_pointert other) const
{
  abstract_objectt::locationst location_union = get_location_union(
      other->get_last_written_locations());

  // If the union is larger than the initial set, then update.
  if(location_union.size() > get_last_written_locations().size())
  {
    abstract_object_pointert result = mutable_clone();
    return result->update_last_written_locations(location_union, false);
  }
  return shared_from_this();
}

/**
 * Sets the last written locations for this context
 *
 * \param locations the locations to set
 */
void dependency_context_abstract_objectt::set_last_written_locations(
  const abstract_objectt::locationst &locations)
{
  last_written_locations=locations;
}

/**
 * Try to resolve an expression with the maximum level of precision
 * available.
 *
 * \param expr the expression to evaluate and find the result of. This will
 * be the symbol referred to be op0()
 * \param environment the abstract environment in which to resolve 'expr'
 * \param ns the current namespace
 *
 * \return the resolved expression
 */
abstract_object_pointert
  dependency_context_abstract_objectt::expression_transform(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns) const
{
  return child_abstract_object->expression_transform(expr, environment, ns);
}

/**
 * Output a representation of the value of this abstract object
 *
 * \param out the stream to write to
 * \param ai the abstract interpreter that contains the abstract domain
 * (that contains the object ... )
 * \param ns the current namespace
 */
void dependency_context_abstract_objectt::output(
  std::ostream &out, const ai_baset &ai, const namespacet &ns) const
{
  child_abstract_object->output(out, ai, ns);

  // Output last written locations immediately following the child output
  out << " @ ";
  output_last_written_locations(out, last_written_locations);
}

/**
 * Construct the union of the location set of the current object, and a
 * the provided location set.
 *
 * \param locations the set of locations to be unioned with this context
 *
 * \return the union of this objects location set, and 'locations'
 */
abstract_objectt::locationst
  dependency_context_abstract_objectt::get_location_union(
    const locationst &locations) const
{
  locationst existing_locations=get_last_written_locations();
  existing_locations.insert(locations.begin(), locations.end());

  return existing_locations;
}

/**
 * Internal helper function to format and output a given set of locations
 *
 * \param out the stream on which to output the locations
 * \param locations the set of locations to output
 */
void dependency_context_abstract_objectt::output_last_written_locations(
  std::ostream &out,
  const abstract_objectt::locationst &locations)
{
  out << "[";
  bool comma=false;

  std::set<unsigned> sorted_locations;
  for(auto location : locations)
  {
    sorted_locations.insert(location->location_number);
  }

  for(auto location_number : sorted_locations)
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
