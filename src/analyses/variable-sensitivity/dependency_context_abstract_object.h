/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Chris Ryder, chris.ryder@diffblue.com

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_DEPENDENCY_CONTEXT_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_DEPENDENCY_CONTEXT_ABSTRACT_OBJECT_H

#include <stack>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <iostream>
#include "array_abstract_object.h"

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
class dependency_context_abstract_objectt: public abstract_objectt
{
public:
  // These constructors mirror those in the base abstract_objectt, but with
  // the addition of an extra argument which is the abstract_objectt to wrap.
  explicit dependency_context_abstract_objectt(
    const abstract_object_pointert child,
    const typet &type):
      abstract_objectt(type)
  {
    child_abstract_object = child;
  }

  dependency_context_abstract_objectt(
    const abstract_object_pointert child,
    const typet &type,
    bool top,
    bool bottom):
      abstract_objectt(type, top, bottom)
  {
    child_abstract_object = child;
  }

  explicit dependency_context_abstract_objectt(
    const abstract_object_pointert child,
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns):
      abstract_objectt(expr, environment, ns)
  {
    child_abstract_object = child;
  }

  virtual ~dependency_context_abstract_objectt() {}

  // Standard abstract_objectt interface

  virtual bool has_been_modified(const abstract_object_pointert before) const
    override;

  virtual abstract_object_pointert update_location_context(
    const abstract_objectt::locationst &locations,
    const bool update_sub_elements) const override;

  // A visitor class to update the last_written_locations of any visited
  // abstract_object with a given set of locations.
  class location_update_visitort:
    public abstract_objectt::abstract_object_visitort
  {
  public:
    explicit location_update_visitort(const locationst &locations):
      locations(locations) { }

    abstract_object_pointert visit(const abstract_object_pointert element) const
    {
      return element->update_location_context(locations, true);
    }

  private:
    const locationst &locations;
  };

  locationst get_location_union(const locationst &locations) const;

  virtual const typet &type() const
  {
    return child_abstract_object->type();
  }

  virtual bool is_top() const override
  {
    return child_abstract_object->is_top();
  }

  virtual bool is_bottom() const override
  {
    return child_abstract_object->is_bottom();
  }

  abstract_object_pointert expression_transform(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns) const;

  virtual exprt to_constant() const override
  {
    return child_abstract_object->to_constant();
  }

  virtual void output(
    std::ostream &out, const class ai_baset &ai, const namespacet &ns) const
  override;


protected:
  CLONE

  virtual abstract_object_pointert merge(
    abstract_object_pointert other) const override;

  virtual abstract_object_pointert read(
    const abstract_environmentt &env,
    const exprt &specifier,
    const namespacet &ns) const override;

  virtual abstract_object_pointert write(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> stack,
    const exprt &specifier,
    const abstract_object_pointert value,
    bool merging_write) const override;

  static void output_last_written_locations(
    std::ostream &out,
    const abstract_objectt::locationst &locations);

  virtual abstract_objectt::locationst get_last_written_locations() const;

private:
  // To enforce copy-on-write these are private and have read-only accessors
  abstract_objectt::locationst last_written_locations;
  abstract_object_pointert child_abstract_object;

  // These are internal hooks that allow sub-classes to perform additional
  // actions when an abstract_object is set/unset to TOP
  virtual void make_top_internal() override;
  virtual void clear_top_internal() override;

  virtual abstract_object_pointert abstract_object_merge_internal(
    const abstract_object_pointert other) const override;

  void set_last_written_locations(
    const abstract_objectt::locationst &locations);

  void set_child(
    const abstract_object_pointert &child);
};


/**
 * Templated extension of the abstract implementation, used as a wrapper around
 * other abstract_objectt classes to enable the factory to instantiate the
 * context information
 */
template <class AOT>
class context_abstract_objectt: public dependency_context_abstract_objectt
{
public:
  explicit context_abstract_objectt(const typet &type):
    dependency_context_abstract_objectt(
      abstract_object_pointert(new AOT(type)), type) {}

  context_abstract_objectt(
    const typet &type,
    bool top,
    bool bottom):
      dependency_context_abstract_objectt(
        abstract_object_pointert(new AOT(type, top, bottom)),
          type,
          top,
          bottom) {}

  explicit context_abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns):
      dependency_context_abstract_objectt(
        abstract_object_pointert(new AOT(expr, environment, ns)),
        expr,
        environment,
        ns) {}
};
// NOLINTNEXTLINE(whitespace/line_length)
#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_DEPENDENCY_CONTEXT_ABSTRACT_OBJECT_H
