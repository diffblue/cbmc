/*******************************************************************\

 Module: analyses variable-sensitivity liveness_contextt

 Author: Jez Higgins

\*******************************************************************/

/**
 * \file
 *  Maintain a context in the variable sensitvity domain that records
 *  the liveness region for a given abstract_objectt.
 */

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_LIVENESS_CONTEXT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_LIVENESS_CONTEXT_H

#include <analyses/variable-sensitivity/write_location_context.h>
#include <iostream>
#include <stack>

/**
 * General implementation of an abstract_objectt which tracks the
 * last written locations for a given abstract_objectt.
 * Instances of this class are constructed with an abstract_object_pointert,
 * to which most operations are delegated, while at the same time this
 * class handles the tracking of the 'last_written_location' information.
 *
 * Instances of this class are best constructed via the templated version
 * of this, 'context_abstract_objectt<T>' which provides the same
 * constructors as the standard 'abstract_objectt' class.
 */
class liveness_contextt : public write_location_contextt
{
public:
  explicit liveness_contextt(
    const abstract_object_pointert child,
    const typet &type)
    : write_location_contextt(child, type)
  {
  }

  liveness_contextt(
    const abstract_object_pointert child,
    const typet &type,
    bool top,
    bool bottom)
    : write_location_contextt(child, type, top, bottom)
  {
  }

  explicit liveness_contextt(
    const abstract_object_pointert child,
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns)
    : write_location_contextt(child, expr, environment, ns)
  {
  }

  abstract_object_pointert
  merge_location_context(const locationt &location) const override;

  void output(std::ostream &out, const class ai_baset &ai, const namespacet &ns)
    const override;

  locationt get_location() const;

protected:
  CLONE

  abstract_object_pointert merge(
    const abstract_object_pointert &other,
    const widen_modet &widen_mode) const override;

  abstract_object_pointert abstract_object_merge_internal(
    const abstract_object_pointert &other) const override;

  abstract_object_pointert write(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const exprt &specifier,
    const abstract_object_pointert &value,
    bool merging_write) const override;

private:
  using liveness_context_ptrt = std::shared_ptr<const liveness_contextt>;

  abstract_object_pointert
  reset_location_on_merge(const liveness_context_ptrt &merged) const;

  optionalt<locationt> assign_location;

  context_abstract_object_ptrt
  update_location_context_internal(const locationst &locations) const override;

  bool has_location() const;

  void set_location(const locationt &location);
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_LIVENESS_CONTEXT_H
