/*******************************************************************\

Module: analyses variable-sensitivity data_dependency_context

Author: Diffblue Ltd

\*******************************************************************/

/**
 * \file
 * Maintain data dependencies as a context in the variable sensitivity domain
 */

#include <algorithm>

#include "data_dependency_context.h"

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
bool data_dependency_contextt::has_been_modified(
  const abstract_object_pointert &before) const
{
  if(this->write_location_contextt::has_been_modified(before))
    return true;

  auto cast_before =
    std::dynamic_pointer_cast<const data_dependency_contextt>(before);

  if(!cast_before)
  {
    // The other context is not something we understand, so must assume
    // that the abstract_object has been modified
    return true;
  }

  // Check whether the data dependencies have changed as well
  abstract_objectt::locationst intersection;
  std::set_intersection(
    data_deps.cbegin(),
    data_deps.cend(),
    cast_before->data_deps.cbegin(),
    cast_before->data_deps.cend(),
    std::inserter(intersection, intersection.end()),
    location_ordert());
  bool all_matched = intersection.size() == data_deps.size() &&
                     intersection.size() == cast_before->data_deps.size();

  if(!all_matched)
    return true;

  intersection.clear();
  std::set_intersection(
    data_dominators.cbegin(),
    data_dominators.cend(),
    cast_before->data_dominators.cbegin(),
    cast_before->data_dominators.cend(),
    std::inserter(intersection, intersection.end()),
    location_ordert());

  all_matched = intersection.size() == data_dominators.size() &&
                intersection.size() == cast_before->data_dominators.size();

  return !all_matched;
}

/**
 * Insert the given set of data dependencies into the data dependencies set
 * for this data_dependency_context object.
 *
 * \param dependencies the set of dependencies to add
 * \return a new data_dependency_context if new dependencies were added,
 * or 'this' if no addtional dependencies were added.
 */
abstract_object_pointert data_dependency_contextt::insert_data_deps(
  const dependencest &dependencies) const
{
  // If this is the first write to the context then it is also used as
  // the initial set of data dependency dominators as well.
  const bool first_write = data_deps.empty();
  dependencest new_dependencies;

  // Workout what new data dependencies need to be inserted
  if(first_write)
  {
    new_dependencies = dependencies;
  }
  else
  {
    std::set_difference(
      dependencies.begin(),
      dependencies.end(),
      data_deps.begin(),
      data_deps.end(),
      std::inserter(new_dependencies, new_dependencies.begin()),
      location_ordert{});
  }

  // If there are no new dependencies to add, just return
  if(new_dependencies.empty())
    return shared_from_this();

  const auto &result =
    std::dynamic_pointer_cast<data_dependency_contextt>(mutable_clone());

  for(auto l : new_dependencies)
  {
    result->data_deps.insert(l);
  }

  if(first_write)
  {
    // If this was the first insertion of any dependencies, then these
    // data dependencies are also data dominators as well
    for(auto l : new_dependencies)
    {
      result->data_dominators.insert(l);
    }
  }
  return result;
}

/**
 * Set the given set of data dependencies for this data_dependency_context
 * object.
 *
 * \param dependencies the set of dependencies to set
 * \return a new data_dependency_context if new dependencies were set,
 * or 'this' if the dependencies were not changed.
 */
abstract_object_pointert
data_dependency_contextt::set_data_deps(const dependencest &dependencies) const
{
  // If the dependencies will not change, just return 'this'
  abstract_objectt::locationst intersection;

  std::set_intersection(
    data_deps.cbegin(),
    data_deps.cend(),
    dependencies.cbegin(),
    dependencies.cend(),
    std::inserter(intersection, intersection.end()),
    location_ordert());
  if(
    intersection.size() == data_deps.size() &&
    intersection.size() == dependencies.size())
    return shared_from_this();

  const auto &result =
    std::dynamic_pointer_cast<data_dependency_contextt>(mutable_clone());

  result->data_deps = dependencies;

  // If this is the first write to the context then it is also used as
  // the initial set of data dependency dominators as well.
  if(data_deps.empty())
  {
    result->data_dominators = dependencies;
  }
  return result;
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
abstract_object_pointert data_dependency_contextt::write(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const exprt &specifier,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  const auto updated_parent =
    std::dynamic_pointer_cast<const data_dependency_contextt>(
      this->write_location_contextt::write(
        environment, ns, stack, specifier, value, merging_write));

  const auto cast_value =
    std::dynamic_pointer_cast<const data_dependency_contextt>(value);

  return updated_parent->set_data_deps(cast_value->data_deps);
}

/**
 * Update the location context for an abstract object, potentially
 * propogating the update to any children of this abstract object.
 *
 * \param locations the set of locations to be updated
 * \param update_sub_elements if true, propogate the update operation to any
 * children of this abstract object
 *
 * \return a clone of this abstract object with its location context
 * updated
 */
abstract_object_pointert data_dependency_contextt::update_location_context(
  const abstract_objectt::locationst &locations,
  const bool update_sub_elements) const
{
  const auto updated_parent =
    std::dynamic_pointer_cast<const data_dependency_contextt>(
      this->write_location_contextt::update_location_context(
        locations, update_sub_elements));

  return updated_parent->set_data_deps(locations);
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
abstract_object_pointert data_dependency_contextt::merge(
  const abstract_object_pointert &other,
  const widen_modet &widen_mode) const
{
  auto cast_other =
    std::dynamic_pointer_cast<const data_dependency_contextt>(other);

  if(cast_other)
  {
    const auto merged_parent =
      std::dynamic_pointer_cast<const data_dependency_contextt>(
        this->write_location_contextt::merge(other, widen_mode));

    return combine(cast_other, merged_parent);
  }

  return abstract_objectt::merge(other, widen_mode);
}

abstract_object_pointert
data_dependency_contextt::meet(const abstract_object_pointert &other) const
{
  auto cast_other =
    std::dynamic_pointer_cast<const data_dependency_contextt>(other);

  if(cast_other)
  {
    const auto meet_parent =
      std::dynamic_pointer_cast<const data_dependency_contextt>(
        this->write_location_contextt::meet(other));

    return combine(cast_other, meet_parent);
  }

  return abstract_objectt::meet(other);
}

abstract_object_pointert data_dependency_contextt::combine(
  const data_dependency_context_ptrt &other,
  const data_dependency_context_ptrt &parent) const
{
  const auto updated_parent =
    std::dynamic_pointer_cast<const data_dependency_contextt>(
      parent->insert_data_deps(other->data_deps));

  const auto &result = std::dynamic_pointer_cast<data_dependency_contextt>(
    updated_parent->mutable_clone());

  // On a merge, data_dominators are the intersection of this object and the
  // other object. In other words, the dominators at this merge point are
  // those dominators that exist in all possible execution paths to this
  // merge point.
  result->data_dominators.clear();
  std::set_intersection(
    data_dominators.begin(),
    data_dominators.end(),
    other->data_dominators.begin(),
    other->data_dominators.end(),
    std::inserter(result->data_dominators, result->data_dominators.end()),
    location_ordert());

  // It is critically important that we only return a newly constructed result
  // abstract object *iff* the data has actually changed, otherwise AI may
  // never reach a fixpoint
  bool value_change = get_child() != result->get_child();
  if(value_change || has_been_modified(result))
    return result;
  else
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
data_dependency_contextt::abstract_object_merge_internal(
  const abstract_object_pointert &other) const
{
  auto other_context =
    std::dynamic_pointer_cast<const data_dependency_contextt>(other);

  if(other_context)
  {
    const auto merged_parent =
      std::dynamic_pointer_cast<const data_dependency_contextt>(
        this->write_location_contextt::abstract_object_merge_internal(other));

    return merged_parent->insert_data_deps(other_context->data_deps);
  }
  return shared_from_this();
}

/**
 * Return the set of data dependencies associated with this node
 *
 * \return set of data dependencies
 */
std::set<goto_programt::const_targett>
data_dependency_contextt::get_data_dependencies() const
{
  std::set<goto_programt::const_targett> result;
  for(const auto &d : data_deps)
    result.insert(d);
  return result;
}

/**
 * Return the set of data dominators associated with this node
 *
 * \return set of data dominators
 */
std::set<goto_programt::const_targett>
data_dependency_contextt::get_data_dominators() const
{
  std::set<goto_programt::const_targett> result;
  for(const auto &d : data_dominators)
    result.insert(d);
  return result;
}

void data_dependency_contextt::output(
  std::ostream &out,
  const class ai_baset &ai,
  const namespacet &ns) const
{
  this->write_location_contextt::output(out, ai, ns);

  out << "[Data dependencies: ";

  bool comma = false;
  for(auto d : data_deps)
  {
    out << (comma ? ", " : "") << d->location_number;
    comma = true;
  }
  out << ']';

  out << "[Data dominators: ";

  comma = false;
  for(auto d : data_dominators)
  {
    out << (comma ? ", " : "") << d->location_number;
    comma = true;
  }
  out << ']';
}
