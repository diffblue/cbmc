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

  virtual exprt to_constant() const override;

  virtual void output(
    std::ostream &out,
    const class ai_baset &ai,
    const class namespacet &ns) const override;

protected:
  CLONE
  virtual const abstract_objectt *merge(abstract_object_pointert other) const override;

private :
  const abstract_objectt *merge_constant_constant(
    constant_abstract_value_pointert other) const;

  exprt value;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_ABSTRACT_VALUE_H
