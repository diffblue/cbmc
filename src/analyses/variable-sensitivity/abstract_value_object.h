/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

/// \file
/// Common behaviour for abstract objects modelling values -
/// constants, intervals, etc.
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_VALUE_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_VALUE_OBJECT_H

#include <analyses/variable-sensitivity/abstract_object.h>

class abstract_value_tag
{
};

class index_ranget
{
public:
  virtual ~index_ranget() = default;
  virtual const exprt &current() const = 0;
  virtual bool advance_to_next() = 0;
};

class single_value_index_ranget : public index_ranget
{
protected:
  explicit single_value_index_ranget(const exprt &val);

public:
  const exprt &current() const override;
  bool advance_to_next() override;

private:
  const exprt value;
  bool available;
};

typedef std::shared_ptr<index_ranget> index_range_ptrt;

index_range_ptrt make_empty_index_range();
index_range_ptrt make_indeterminate_index_range();

class abstract_value_objectt : public abstract_objectt,
                               public abstract_value_tag
{
public:
  explicit abstract_value_objectt(const typet &type) : abstract_objectt(type)
  {
  }

  abstract_value_objectt(const typet &type, bool tp, bool bttm)
    : abstract_objectt(type, tp, bttm)
  {
  }

  abstract_value_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns)
    : abstract_objectt(expr, environment, ns)
  {
  }

  virtual index_range_ptrt index_range(const namespacet &ns) const = 0;
};

#endif