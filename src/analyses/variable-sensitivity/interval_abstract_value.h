/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_INTERVAL_ABSTRACT_VALUE_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_INTERVAL_ABSTRACT_VALUE_H

#include <iosfwd>

#include <util/interval.h>

#include <analyses/variable-sensitivity/abstract_value.h>
#include <util/std_expr.h>

class interval_abstract_valuet:public abstract_valuet
{
private:
  typedef sharing_ptrt<interval_abstract_valuet>
    interval_abstract_value_pointert;
  static inline constant_interval_exprt make_interval_expr(exprt e) {
    if(e.id() == ID_constant_interval) {
      return to_constant_interval_expr(e);
    } else {
      return constant_interval_exprt(e, e);
    }
  }
public:
  explicit interval_abstract_valuet(typet t);
  interval_abstract_valuet(typet t, bool tp, bool bttm);
  interval_abstract_valuet(
    const constant_interval_exprt e);
  interval_abstract_valuet(
    const exprt e,
    const abstract_environmentt &environment,
    const namespacet &ns)
  : interval_abstract_valuet(make_interval_expr(e))
  {

  }

  virtual ~interval_abstract_valuet() {}

  virtual exprt to_constant() const override;

#if 1
  // Interface for transforms
  abstract_object_pointert expression_transform(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns) const override;
#endif

  virtual void output(
    std::ostream &out,
    const class ai_baset &ai,
    const class namespacet &ns) const override;

protected:
  CLONE
  virtual abstract_object_pointert merge(
    abstract_object_pointert other) const override;

private :
  abstract_object_pointert merge_interval_interval(
    interval_abstract_value_pointert other) const;

  constant_interval_exprt interval;
  //exprt value;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_INTERVAL_ABSTRACT_VALUE_H
