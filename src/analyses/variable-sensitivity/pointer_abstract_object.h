/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_POINTER_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_POINTER_ABSTRACT_OBJECT_H


#include <stack>

#include <analyses/variable-sensitivity/abstract_object.h>

class typet;
class constant_exprt;
class abstract_environmentt;

class pointer_abstract_objectt:public abstract_objectt
{
public:
  explicit pointer_abstract_objectt(const typet &type);
  pointer_abstract_objectt(const typet &type, bool top, bool bottom);
  explicit pointer_abstract_objectt(
    const exprt &e,
    const abstract_environmentt &environment,
    const namespacet &ns);

  // pointer interface
  virtual abstract_object_pointert read_dereference(
    const abstract_environmentt &env, const namespacet &ns) const;

  virtual sharing_ptrt<pointer_abstract_objectt> write_dereference(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> stack,
    const abstract_object_pointert value,
    bool merging_write) const;

protected:
  CLONE
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_POINTER_ABSTRACT_OBJECT_H
