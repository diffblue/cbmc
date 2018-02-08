/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_STRUCT_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_STRUCT_ABSTRACT_OBJECT_H

#include <stack>
#include <analyses/variable-sensitivity/abstract_object.h>

class abstract_environmentt;
class member_exprt;

class struct_abstract_objectt:public abstract_objectt
{
public:
  explicit struct_abstract_objectt(const typet &type);
  struct_abstract_objectt(const typet &type, bool top, bool bottom);
  explicit struct_abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

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

protected:
  CLONE

  // struct interface
  virtual abstract_object_pointert read_component(
    const abstract_environmentt &environment,
    const member_exprt &member_expr,
    const namespacet &ns) const;

  virtual sharing_ptrt<struct_abstract_objectt> write_component(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const member_exprt &member_expr,
    const abstract_object_pointert value,
    bool merging_write) const;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_STRUCT_ABSTRACT_OBJECT_H
