/*******************************************************************\

 Module: analyses variable-sensitivity context_abstract_object

 Author: Diffblue Ltd

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONTEXT_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONTEXT_ABSTRACT_OBJECT_H

#include <analyses/variable-sensitivity/abstract_object.h>

/**
 * \file
 * General implementation of a an abstract_objectt which can track
 * side information in the form of a 'context' associated with a wrapped
 * abstract_objectt of some other type. This class is not intended to be
 * instantiated directly - instead it is intended to be inherited from for
 * other classes to define what the context actually means.
 */
class context_abstract_objectt : public abstract_objectt
{
public:
  // These constructors mirror those in the base abstract_objectt, but with
  // the addition of an extra argument which is the abstract_objectt to wrap.
  explicit context_abstract_objectt(
    const abstract_object_pointert child,
    const typet &type)
    : abstract_objectt(type)
  {
    child_abstract_object = child;
  }

  context_abstract_objectt(
    const abstract_object_pointert child,
    const typet &type,
    bool top,
    bool bottom)
    : abstract_objectt(type, top, bottom)
  {
    child_abstract_object = child;
  }

  explicit context_abstract_objectt(
    const abstract_object_pointert child,
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns)
    : abstract_objectt(expr, environment, ns)
  {
    child_abstract_object = child;
  }

  virtual ~context_abstract_objectt()
  {
  }

  const typet &type() const override
  {
    return child_abstract_object->type();
  }

  bool is_top() const override
  {
    return child_abstract_object->is_top();
  }

  bool is_bottom() const override
  {
    return child_abstract_object->is_bottom();
  }

  exprt to_constant() const override
  {
    return child_abstract_object->to_constant();
  }

  abstract_object_pointert expression_transform(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const override;

  void output(std::ostream &out, const class ai_baset &ai, const namespacet &ns)
    const override;

  abstract_object_pointert envelop(abstract_object_pointert &child) const;
  abstract_object_pointert unwrap_context() const override;

  void get_statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns) const override;

  abstract_object_pointert get_child() const;

protected:
  CLONE

  // The abstract_objectt that will be wrapped in a context
  abstract_object_pointert child_abstract_object;

  void set_child(const abstract_object_pointert &child);

  // These are internal hooks that allow sub-classes to perform additional
  // actions when an abstract_object is set/unset to TOP
  void set_top_internal() override;
  void set_not_top_internal() override;

  abstract_object_pointert write(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const exprt &specifier,
    const abstract_object_pointert &value,
    bool merging_write) const override;

  bool has_been_modified(const abstract_object_pointert &before) const override;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONTEXT_ABSTRACT_OBJECT_H
