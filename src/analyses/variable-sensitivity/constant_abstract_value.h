/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_ABSTRACT_VALUE_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_ABSTRACT_VALUE_H

#include <iosfwd>

#include <analyses/variable-sensitivity/abstract_value.h>
#include <util/std_expr.h>

class constant_abstract_valuet:public abstract_valuet
{
private:
  typedef sharing_ptrt<constant_abstract_valuet>
    constant_abstract_value_pointert;

public:
  explicit constant_abstract_valuet(typet t);
  constant_abstract_valuet(typet t, bool tp, bool bttm);
  constant_abstract_valuet(
    const exprt e,
    const abstract_environmentt &environment,
    const namespacet &ns);

  virtual ~constant_abstract_valuet() {}

  virtual abstract_object_pointert expression_transform(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const override;

  virtual exprt to_constant() const override;

  virtual void output(
    std::ostream &out,
    const class ai_baset &ai,
    const class namespacet &ns) const override;

  void get_statistics(abstract_object_statisticst &statistics,
                      abstract_object_visitedt &visited,
                      const abstract_environmentt &env,
                      const namespacet& ns) const override;

protected:
  CLONE
  virtual abstract_object_pointert merge(
    abstract_object_pointert other) const override;

  abstract_object_pointert try_transform_expr_with_all_rounding_modes(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns) const;

private :
  abstract_object_pointert merge_constant_constant(
    constant_abstract_value_pointert other) const;

  exprt value;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_ABSTRACT_VALUE_H
