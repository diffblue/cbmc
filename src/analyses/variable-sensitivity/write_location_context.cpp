/*******************************************************************\

 Module: analyses variable-sensitivity write_location_context

 Author: Diffblue Ltd.

\*******************************************************************/

#include "write_location_context.h"

#include <algorithm>

/**
 * Update the location context for an abstract object, potentially
 * propagating the update to any children of this abstract object.
 *
 * \param locations the set of locations to be updated
 * \param update_sub_elements if true, propogate the update operation to any
 * children of this abstract object
 *
 * \return a clone of this abstract object with its location context
 * updated
 */
abstract_object_pointert write_location_contextt::update_location_context(
  const abstract_objectt::locationst &locations,
  const bool update_sub_elements) const
{
  const auto &result =
    std::dynamic_pointer_cast<write_location_contextt>(mutable_clone());

  if(update_sub_elements)
  {
    abstract_object_pointert visited_child =
      child_abstract_object
        ->update_location_context(locations, update_sub_elements)
        ->visit_sub_elements(location_update_visitort(locations));
    result->set_child(visited_child);
  }

  result->set_last_written_locations(locations);
  return result;
}

abstract_objectt::locationst
write_location_contextt::get_last_written_locations() const
{
  return last_written_locations;
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
abstract_object_pointert write_location_contextt::write(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const exprt &specifier,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  abstract_object_pointert updated_child = child_abstract_object->write(
    environment, ns, stack, specifier, value, merging_write);

  // Only perform an update if the write to the child has in fact changed it...
  if(updated_child == child_abstract_object)
    return shared_from_this();

  // Need to ensure the result of the write is still wrapped in a dependency
  // context
  const auto &result =
    std::dynamic_pointer_cast<write_location_contextt>(mutable_clone());

  // Update the child and record the updated write locations
  result->set_child(updated_child);
  auto value_context =
    std::dynamic_pointer_cast<const write_location_contextt>(value);

  if(value_context)
  {
    result->set_last_written_locations(
      value_context->get_last_written_locations());
  }

  return result;
}

/**
 * Create a new abstract object that is the result of merging this abstract
 * object with a given abstract_object
 *
 * \param other the abstract object to merge with
 * \param widen_mode: Indicates if this is a widening merge
 *
 * \return the result of the merge, or 'this' if the merge would not change
 * the current abstract object
 */
abstract_object_pointert write_location_contextt::merge(
  const abstract_object_pointert &other,
  const widen_modet &widen_mode) const
{
  auto cast_other =
    std::dynamic_pointer_cast<const write_location_contextt>(other);

  if(cast_other)
  {
    auto merge_fn = [&widen_mode](
                      const abstract_object_pointert &op1,
                      const abstract_object_pointert &op2) {
      return abstract_objectt::merge(op1, op2, widen_mode);
    };
    return combine(cast_other, merge_fn);
  }

  return abstract_objectt::merge(other, widen_mode);
}

// need wrapper function here to disambiguate meet overload
abstract_objectt::combine_result object_meet(
  const abstract_object_pointert &op1,
  const abstract_object_pointert &op2)
{
  return abstract_objectt::meet(op1, op2);
}

abstract_object_pointert
write_location_contextt::meet(const abstract_object_pointert &other) const
{
  auto cast_other =
    std::dynamic_pointer_cast<const write_location_contextt>(other);

  if(cast_other)
    return combine(cast_other, object_meet);

  return abstract_objectt::meet(other);
}

abstract_object_pointert write_location_contextt::combine(
  const write_location_context_ptrt &other,
  combine_fn fn) const
{
  auto combined_child = fn(child_abstract_object, other->child_abstract_object);

  abstract_objectt::locationst location_union =
    get_location_union(other->get_last_written_locations());
  // If the union is larger than the initial set, then update.
  bool merge_locations =
    location_union.size() > get_last_written_locations().size();

  if(combined_child.modified || merge_locations)
  {
    const auto &result =
      std::dynamic_pointer_cast<write_location_contextt>(mutable_clone());
    if(combined_child.modified)
    {
      result->set_child(combined_child.object);
    }
    if(merge_locations)
    {
      result->set_last_written_locations(location_union);
    }

    return result;
  }

  return shared_from_this();
}

/**
 * Helper function for abstract_objectt::abstract_object_merge to perform any
 * additional actions after the base abstract_object_merge has completed its
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
write_location_contextt::abstract_object_merge_internal(
  const abstract_object_pointert &other) const
{
  auto other_context =
    std::dynamic_pointer_cast<const write_location_contextt>(other);

  if(other_context)
  {
    abstract_objectt::locationst location_union =
      get_location_union(other_context->get_last_written_locations());

    // If the union is larger than the initial set, then update.
    if(location_union.size() > get_last_written_locations().size())
    {
      abstract_object_pointert result = mutable_clone();
      return result->update_location_context(location_union, false);
    }
  }
  return shared_from_this();
}

/**
 * Sets the last written locations for this context
 *
 * \param locations the locations to set
 */
void write_location_contextt::set_last_written_locations(
  const abstract_objectt::locationst &locations)
{
  last_written_locations = locations;
}

/**
 * Output a representation of the value of this abstract object
 *
 * \param out the stream to write to
 * \param ai the abstract interpreter that contains the abstract domain
 * (that contains the object ... )
 * \param ns the current namespace
 */
void write_location_contextt::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  context_abstract_objectt::output(out, ai, ns);

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
write_location_contextt::get_location_union(const locationst &locations) const
{
  locationst existing_locations = get_last_written_locations();
  existing_locations.insert(locations.begin(), locations.end());

  return existing_locations;
}

/**
 * Determine whether 'this' abstract_object has been modified in comparison
 * to a previous 'before' state.
 *
 * \param before the abstract_object_pointert to use as a reference to
 * compare against
 *
 * \return true if 'this' is considered to have been modified in comparison
 * to 'before', false otherwise.
 */
bool write_location_contextt::has_been_modified(
  const abstract_object_pointert &before) const
{
  if(this == before.get())
  {
    // copy-on-write means pointer equality implies no modifications
    return false;
  }

  auto before_context =
    std::dynamic_pointer_cast<const write_location_contextt>(before);

  if(!before_context)
  {
    // The other context is not something we understand, so must assume
    // that the abstract_object has been modified
    return true;
  }

  // Even if the pointers are different, it maybe that it has changed only
  // because of a merge operation, rather than an actual write. Given that
  // this class has knowledge of where writes have occured, use that
  // information to determine if any writes have happened and use that as the
  // proxy for whether the value has changed or not.
  //
  // For two sets of last written locations to match,
  // each location in one set must be equal to precisely one location
  // in the other, since a set can assume at most one match
  const abstract_objectt::locationst &first_write_locations =
    before_context->get_last_written_locations();
  const abstract_objectt::locationst &second_write_locations =
    get_last_written_locations();

  class location_ordert
  {
  public:
    bool operator()(
      goto_programt::const_targett instruction,
      goto_programt::const_targett other_instruction) const
    {
      return instruction->location_number > other_instruction->location_number;
    }
  };

  typedef std::set<goto_programt::const_targett, location_ordert>
    sorted_locationst;

  sorted_locationst lhs_location;
  for(const auto &entry : first_write_locations)
  {
    lhs_location.insert(entry);
  }

  sorted_locationst rhs_location;
  for(const auto &entry : second_write_locations)
  {
    rhs_location.insert(entry);
  }

  abstract_objectt::locationst intersection;
  std::set_intersection(
    lhs_location.cbegin(),
    lhs_location.cend(),
    rhs_location.cbegin(),
    rhs_location.cend(),
    std::inserter(intersection, intersection.end()),
    location_ordert());
  bool all_matched = intersection.size() == first_write_locations.size() &&
                     intersection.size() == second_write_locations.size();

  return !all_matched;
}

/**
 * Internal helper function to format and output a given set of locations
 *
 * \param out the stream on which to output the locations
 * \param locations the set of locations to output
 */
void write_location_contextt::output_last_written_locations(
  std::ostream &out,
  const abstract_objectt::locationst &locations)
{
  out << "[";
  bool comma = false;

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
      comma = true;
    }
    else
    {
      out << ", " << location_number;
    }
  }
  out << "]";
}
