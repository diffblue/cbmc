/*******************************************************************\

 Module: analyses variable-sensitivity region_context

 Author: Jez Higgins

\*******************************************************************/

/**
 * \file
 *  Maintain a context in the variable sensitvity domain that records
 *  the assignment region for a given abstract_objectt.
 */

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_REGION_CONTEXT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_REGION_CONTEXT_H

#include <analyses/variable-sensitivity/context_abstract_object.h>
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
class region_contextt : public context_abstract_objectt
{
public:
  explicit region_contextt(
    const abstract_object_pointert child,
    const typet &type)
    : context_abstract_objectt(child, type)
  {
  }

  region_contextt(
    const abstract_object_pointert child,
    const typet &type,
    bool top,
    bool bottom)
    : context_abstract_objectt(child, type, top, bottom)
  {
  }

  explicit region_contextt(
    const abstract_object_pointert child,
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns)
    : context_abstract_objectt(child, expr, environment, ns)
  {
  }

  virtual ~region_contextt()
  {
  }

  bool has_been_modified(const abstract_object_pointert &before) const override;

  void output(std::ostream &out, const class ai_baset &ai, const namespacet &ns)
    const override;

protected:
  CLONE

  abstract_object_pointert merge(
    const abstract_object_pointert &other,
    const widen_modet &widen_mode) const override;
  abstract_object_pointert
  meet(const abstract_object_pointert &other) const override;

  abstract_object_pointert write(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const exprt &specifier,
    const abstract_object_pointert &value,
    bool merging_write) const override;

  locationt get_location() const;
  void reset_location();

private:
  using combine_fn = std::function<abstract_objectt::combine_result(
    const abstract_object_pointert &op1,
    const abstract_object_pointert &op2)>;
  using region_context_ptrt = std::shared_ptr<const region_contextt>;

  abstract_object_pointert
  combine(const region_context_ptrt &other, combine_fn fn) const;

  optionalt<locationt> assign_location;

  context_abstract_object_ptrt
  update_location_context_internal(const locationst &locations) const override;

  void set_location(const locationt &location);
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_REGION_CONTEXT_H
