/*******************************************************************\

 Module: analyses variable-sensitivity region_contextt

 Author: Jez Higgins

\*******************************************************************/

#include "liveness_context.h"

bool liveness_contextt::has_location() const
{
  return assign_location.has_value();
}

abstract_objectt::locationt liveness_contextt::get_location() const
{
  return assign_location.value();
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
abstract_object_pointert liveness_contextt::write(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const exprt &specifier,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  auto updated = std::dynamic_pointer_cast<const liveness_contextt>(
    write_location_contextt::write(
      environment, ns, stack, specifier, value, merging_write));
  if(updated == shared_from_this())
    return shared_from_this();

  // record the updated write locations
  auto result =
    std::dynamic_pointer_cast<liveness_contextt>(updated->mutable_clone());
  auto value_context =
    std::dynamic_pointer_cast<const liveness_contextt>(value);
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
abstract_object_pointert liveness_contextt::merge(
  const abstract_object_pointert &other,
  const widen_modet &widen_mode) const
{
  auto cast_other = std::dynamic_pointer_cast<const liveness_contextt>(other);

  if(cast_other)
  {
    auto merged = std::dynamic_pointer_cast<const liveness_contextt>(
      write_location_contextt::merge(other, widen_mode));
    return reset_location_on_merge(merged);
  }

  return abstract_objectt::merge(other, widen_mode);
}

abstract_object_pointert liveness_contextt::abstract_object_merge_internal(
  const abstract_object_pointert &other) const
{
  auto merged = std::dynamic_pointer_cast<const liveness_contextt>(
    write_location_contextt::abstract_object_merge_internal(other));
  return reset_location_on_merge(merged);
}

abstract_object_pointert liveness_contextt::reset_location_on_merge(
  const liveness_context_ptrt &merged) const
{
  if(merged == shared_from_this())
    return shared_from_this();

  auto updated =
    std::dynamic_pointer_cast<liveness_contextt>(merged->mutable_clone());
  updated->assign_location.reset();
  return updated;
}

context_abstract_objectt::context_abstract_object_ptrt
liveness_contextt::update_location_context_internal(
  const locationst &locations) const
{
  auto result = std::dynamic_pointer_cast<liveness_contextt>(mutable_clone());
  result->set_last_written_locations(locations);
  result->set_location(*locations.cbegin());
  return result;
}

void liveness_contextt::set_location(const locationt &location)
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
void liveness_contextt::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  context_abstract_objectt::output(out, ai, ns);

  if(has_location())
    out << " @ [" << get_location()->location_number << "]";
  else
    out << " @ [undefined]";
}

abstract_object_pointert
liveness_contextt::merge_location_context(const locationt &location) const
{
  if(assign_location.has_value())
    return shared_from_this();

  auto update = std::dynamic_pointer_cast<liveness_contextt>(mutable_clone());
  update->assign_location = location;
  auto updated_child = child_abstract_object->merge_location_context(location);
  update->set_child(updated_child);

  return update;
}
