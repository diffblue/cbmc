/*******************************************************************\

Module: Struct abstract object

Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ONE_LEVEL_STRUCT_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ONE_LEVEL_STRUCT_ABSTRACT_OBJECT_H

#include <stack>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/struct_abstract_object.h>

class abstract_environmentt;
class member_exprt;

class full_struct_abstract_objectt:public struct_abstract_objectt
{
public:
  explicit full_struct_abstract_objectt(const typet &type);

  full_struct_abstract_objectt(const typet &type, bool top, bool bottom);

  explicit full_struct_abstract_objectt(const full_struct_abstract_objectt &old);
  explicit full_struct_abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

  CLONE
  MERGE(struct_abstract_objectt)

  // struct interface
  virtual abstract_object_pointert read_component(
    const abstract_environmentt &environment,
    const member_exprt &member_expr,
    const namespacet& ns) const override;

  virtual sharing_ptrt<struct_abstract_objectt> write_component(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const member_exprt &member_expr,
    const abstract_object_pointert value,
    bool merging_write) const override;

private:
  // no entry means component is top
  typedef std::map<irep_idt, abstract_object_pointert> struct_mapt;
  struct_mapt map;

protected:
  bool verify() const;
  // Set the state of this to the merge result of op1 and op2 and
  // return if the result is different from op1
  bool merge_state(
    const sharing_ptrt<full_struct_abstract_objectt> op1,
    const sharing_ptrt<full_struct_abstract_objectt> op2);

};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ONE_LEVEL_STRUCT_ABSTRACT_OBJECT_H
