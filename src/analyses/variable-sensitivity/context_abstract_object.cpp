/*******************************************************************\

 Module: analyses variable-sensitivity context_abstract_object

 Author: Diffblue Ltd

\*******************************************************************/

#include "context_abstract_object.h"


void context_abstract_objectt::set_child(
  const abstract_object_pointert &child)
{
  child_abstract_object = child;
}

void context_abstract_objectt::make_top_internal()
{
  if(!child_abstract_object->is_top())
    set_child(child_abstract_object->make_top());
}

void context_abstract_objectt::clear_top_internal()
{
  if(child_abstract_object->is_top())
    set_child(child_abstract_object->clear_top());
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
abstract_object_pointert context_abstract_objectt::read(
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
abstract_object_pointert context_abstract_objectt::write(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> stack,
  const exprt &specifier,
  const abstract_object_pointert value,
  bool merging_write) const
{
  abstract_object_pointert updated_child=
    child_abstract_object->write(
      environment, ns, stack, specifier, value, merging_write);

  // Only perform an update if the write to the child has in fact changed it...
  if(updated_child == child_abstract_object)
    return shared_from_this();

  // Need to ensure the result of the write is still wrapped in a context
  const auto &result=
    std::dynamic_pointer_cast<context_abstract_objectt>(
      mutable_clone());

  // Update the child and record the updated write locations
  result->set_child(updated_child);

  return result;
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
abstract_object_pointert context_abstract_objectt::expression_transform(
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
void context_abstract_objectt::output(
  std::ostream &out, const ai_baset &ai, const namespacet &ns) const
{
  child_abstract_object->output(out, ai, ns);
}

/**
  * Determine whether 'this' abstract_object has been modified in comparison
  * to a previous 'before' state.
  * \param before The abstract_object_pointert to use as a reference to
  * compare against
  * \return true if 'this' is considered to have been modified in comparison
  * to 'before', false otherwise.
  */
bool context_abstract_objectt::has_been_modified(
  const abstract_object_pointert before) const
{
  // Default implementation, with no other information to go on
  // falls back to relying on copy-on-write and pointer inequality
  // to indicate if an abstract_objectt has been modified
  auto before_context=
    std::dynamic_pointer_cast<const context_abstract_objectt>
      (before);

  return this->child_abstract_object.get() !=
         before_context->child_abstract_object.get();
};
