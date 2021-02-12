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
  class iterator
  {
  public:
    const exprt &operator*() const
    {
      return range->current();
    }
    void operator++()
    {
      active = range->advance_to_next();
    }
    bool operator==(const iterator &other) const
    {
      if(!active && !other.active)
        return true;
      return false;
    }
    bool operator!=(const iterator &other) const
    {
      return !operator==(other);
    }

    iterator(iterator &&rhs) : range(rhs.range), active(rhs.active)
    {
    }
    iterator(const iterator &) = delete;
    ~iterator() = default;

  private:
    iterator() : range(nullptr), active(false)
    {
    }
    explicit iterator(index_ranget *r) : range(r), active(true)
    {
      active = range->advance_to_next();
    }

    index_ranget *range;
    bool active;

    friend class index_ranget;
  };

  virtual ~index_ranget() = default;
  virtual const exprt &current() const = 0;
  virtual bool advance_to_next() = 0;

  iterator begin()
  {
    return iterator{this};
  }
  iterator end() const
  {
    return {};
  }
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

using index_range_ptrt = std::shared_ptr<index_ranget>;

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