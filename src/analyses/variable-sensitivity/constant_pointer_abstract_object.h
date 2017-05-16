/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_POINTER_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_POINTER_ABSTRACT_OBJECT_H

#include <analyses/variable-sensitivity/pointer_abstract_object.h>

class constant_pointer_abstract_objectt:public pointer_abstract_objectt
{
private:
  typedef sharing_ptrt<constant_pointer_abstract_objectt>
    constant_pointer_abstract_pointert;
public:
  constant_pointer_abstract_objectt(const typet &type);

  constant_pointer_abstract_objectt(
    const typet &type,
    bool top,
    bool bottom);

  constant_pointer_abstract_objectt(
    const constant_pointer_abstract_objectt &old);

  constant_pointer_abstract_objectt(const exprt &expr);

  CLONE
  MERGE(pointer_abstract_objectt)

  exprt to_constant() const override;
  void output(
    std::ostream &out, const ai_baset &ai, const namespacet &ns) const override;

  abstract_object_pointert read_dereference(
    const abstract_environmentt &env, const namespacet &ns) const override;

  sharing_ptrt<pointer_abstract_objectt> write_dereference(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> stack,
    const abstract_object_pointert value,
    bool merging_write) override;

protected:
  bool merge_state(
    const constant_pointer_abstract_pointert op1,
    const constant_pointer_abstract_pointert op2);

private:
  exprt value;



};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_POINTER_ABSTRACT_OBJECT_H // NOLINT(*)
