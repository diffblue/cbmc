#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_VALUE_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_VALUE_OBJECT_H

#include <analyses/variable-sensitivity/abstract_object.h>

class abstract_value_tag { };

struct index_ranget {
  virtual ~index_ranget() = default;
  virtual const exprt &current() const = 0;
  virtual bool advance_to_next() = 0;
};

struct empty_index_ranget : index_ranget {
    const exprt &current() const override { return nil; }
    bool advance_to_next() override { return false; }

private:
    exprt nil = nil_exprt();
};

typedef std::shared_ptr<index_ranget> index_range_ptrt;

class abstract_value_objectt :
  public abstract_objectt,
  public abstract_value_tag
{
public:
  explicit abstract_value_objectt(const typet &type)
    : abstract_objectt(type)
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

  virtual index_range_ptrt index_range() const {
     return std::make_shared<empty_index_ranget>();
  }
};

#endif