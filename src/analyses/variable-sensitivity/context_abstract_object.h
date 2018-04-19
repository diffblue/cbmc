/*******************************************************************\

 Module: analyses variable-sensitivity context_abstract_object

 Author: Diffblue Ltd

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONTEXT_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONTEXT_ABSTRACT_OBJECT_H

#include <analyses/variable-sensitivity/abstract_object.h>

/**
 * General implementation of a an abstract_objectt which can track
 * side information in the form of a 'context' associated with a wrapped
 * abstract_objectt of some other type. This class is not intended to be
 * instantiated directly - instead it is intended to be inherited from for
 * other classes to define what the context actually means.
 */
class context_abstract_objectt: public abstract_objectt
{
public:
  // These constructors mirror those in the base abstract_objectt, but with
  // the addition of an extra argument which is the abstract_objectt to wrap.
  explicit context_abstract_objectt(
    const abstract_object_pointert child,
    const typet &type):
    abstract_objectt(type)
  {
    child_abstract_object = child;
  }

  context_abstract_objectt(
    const abstract_object_pointert child,
    const typet &type,
    bool top,
    bool bottom):
    abstract_objectt(type, top, bottom)
  {
    child_abstract_object = child;
  }

  explicit context_abstract_objectt(
    const abstract_object_pointert child,
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns):
    abstract_objectt(expr, environment, ns)
  {
    child_abstract_object = child;
  }

  virtual ~context_abstract_objectt() {}

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

  virtual exprt to_constant() const override
  {
    return child_abstract_object->to_constant();
  }

  abstract_object_pointert expression_transform(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns) const;

  virtual void output(
    std::ostream &out, const class ai_baset &ai, const namespacet &ns) const
  override;

protected:
  CLONE

  // The abstract_objectt that will be wrapped in a context
  abstract_object_pointert child_abstract_object;

  void set_child(
    const abstract_object_pointert &child);

  // These are internal hooks that allow sub-classes to perform additional
  // actions when an abstract_object is set/unset to TOP
  virtual void make_top_internal() override;
  virtual void clear_top_internal() override;

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

  virtual bool has_been_modified(const abstract_object_pointert before) const
    override;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONTEXT_ABSTRACT_OBJECT_H
