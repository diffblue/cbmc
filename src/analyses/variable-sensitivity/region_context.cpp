/*******************************************************************\

 Module: analyses variable-sensitivity region_contextt

 Author: Jez Higgins

\*******************************************************************/

#include "region_context.h"

abstract_objectt::locationt region_contextt::get_location() const
{
  return *assign_location;
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
abstract_object_pointert region_contextt::write(
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
    std::dynamic_pointer_cast<region_contextt>(mutable_clone());

  result->set_child(updated_child);

  // Update the child and record the updated write locations
  auto value_context = std::dynamic_pointer_cast<const region_contextt>(value);
  if(value_context)
    result->set_location(value_context->get_location());

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
abstract_object_pointert region_contextt::merge(
  const abstract_object_pointert &other,
  const widen_modet &widen_mode) const
{
  auto cast_other = std::dynamic_pointer_cast<const region_contextt>(other);

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
region_contextt::meet(const abstract_object_pointert &other) const
{
  auto cast_other = std::dynamic_pointer_cast<const region_contextt>(other);

  if(cast_other)
    return combine(cast_other, object_meet);

  return abstract_objectt::meet(other);
}

abstract_object_pointert
region_contextt::combine(const region_context_ptrt &other, combine_fn fn) const
{
  auto combined_child = fn(child_abstract_object, other->child_abstract_object);
  auto location_match = get_location() == other->get_location();

  if(combined_child.modified || location_match)
  {
    const auto &result =
      std::dynamic_pointer_cast<region_contextt>(mutable_clone());
    result->set_child(combined_child.object);
    result->reset_location();
    return result;
  }

  return shared_from_this();
}

void region_contextt::reset_location()
{
  assign_location.reset();
}

context_abstract_objectt::context_abstract_object_ptrt
region_contextt::update_location_context_internal(
  const locationst &locations) const
{
  auto result = std::dynamic_pointer_cast<region_contextt>(mutable_clone());
  result->set_location(*locations.cbegin());
  return result;
}

void region_contextt::set_location(const locationt &location)
{
  assign_location.emplace(location);
}

/**
 * Output a representation of the value of this abstract object
 *
 * \param out the stream to write to
 * \param ai the abstract interpreter that contains the abstract domain
 * (that contains the object ... )
 * \param ns the current namespace
 */
void region_contextt::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  context_abstract_objectt::output(out, ai, ns);

  if(assign_location.has_value())
    out << " @ [" << assign_location.value()->location_number << "]";
  else
    out << " @ [merge-point]";
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
bool region_contextt::has_been_modified(
  const abstract_object_pointert &before) const
{
  if(this == before.get())
    return false;

  auto before_context =
    std::dynamic_pointer_cast<const region_contextt>(before);

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
  return before_context->get_location() != get_location();
}
