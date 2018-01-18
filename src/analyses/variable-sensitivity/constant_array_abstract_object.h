/*******************************************************************\

 Module: Variable Sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_ARRAY_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_ARRAY_ABSTRACT_OBJECT_H

#include <vector>
#include <iosfwd>

#include <analyses/variable-sensitivity/array_abstract_object.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>

class ai_baset;
class abstract_environmentt;

class constant_array_abstract_objectt:public array_abstract_objectt
{
public:
  typedef sharing_ptrt<constant_array_abstract_objectt> const
    constant_array_pointert;

  explicit constant_array_abstract_objectt(typet type);
  constant_array_abstract_objectt(typet type, bool top, bool bottom);
  constant_array_abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

  virtual ~constant_array_abstract_objectt() {}

  void output(
    std::ostream &out, const ai_baset &ai, const namespacet &ns) const override;

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

  abstract_object_pointert read_index(
    const abstract_environmentt &env,
    const index_exprt &index,
    const namespacet &ns) const;

  sharing_ptrt<array_abstract_objectt> write_index(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> stack,
    const index_exprt &index_expr,
    const abstract_object_pointert value,
    bool merging_write) const;

  virtual abstract_object_pointert merge(
    abstract_object_pointert other) const override;

private:
  // Since we don't store for any index where the value is top
  // we don't use a regular array but instead a map of array indices
  // to the value at that index
  typedef std::map<mp_integer, abstract_object_pointert> array_mapt;
  array_mapt map;

  bool eval_index(
    const index_exprt &index,
    const abstract_environmentt &env,
    const namespacet &ns,
    mp_integer &out_index) const;

  abstract_object_pointert get_top_entry(
    const abstract_environmentt &env, const namespacet &ns) const;

  abstract_object_pointert constant_array_merge(
    const constant_array_pointert other) const;

  virtual void update_sub_elements(const locationst &locations) override;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_ARRAY_ABSTRACT_OBJECT_H
