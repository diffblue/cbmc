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

class index_range_implementationt;

using index_range_implementation_ptrt =
  std::unique_ptr<index_range_implementationt>;

class index_range_implementationt
{
public:
  virtual ~index_range_implementationt() = default;

  virtual index_range_implementation_ptrt reset() const = 0;

  virtual const exprt &current() const = 0;
  virtual bool advance_to_next() = 0;
};

class index_range_iteratort
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
  bool operator==(const index_range_iteratort &other) const
  {
    if(!active && !other.active)
      return true;
    return false;
  }
  bool operator!=(const index_range_iteratort &other) const
  {
    return !operator==(other);
  }

  index_range_iteratort(index_range_iteratort &&rhs)
    : range(std::move(rhs.range)), active(rhs.active)
  {
  }
  index_range_iteratort(const index_range_iteratort &) = delete;
  ~index_range_iteratort() = default;

private:
  index_range_iteratort() : range(nullptr), active(false)
  {
  }
  explicit index_range_iteratort(index_range_implementation_ptrt &&r)
    : range(std::move(r)), active(true)
  {
    active = range->advance_to_next();
  }

  index_range_implementation_ptrt range;
  bool active;

  friend class index_ranget;
};

class index_ranget
{
public:
  explicit index_ranget(index_range_implementation_ptrt r) : range(r.release())
  {
  }
  index_ranget(index_ranget &&rhs) : range(rhs.range.release())
  {
  }
  index_ranget(const index_ranget &) = delete;
  ~index_ranget() = default;

  index_range_iteratort begin() const
  {
    return index_range_iteratort{range->reset()};
  }
  index_range_iteratort end() const
  {
    return {};
  }

private:
  index_range_implementation_ptrt range;
};

class single_value_index_ranget : public index_range_implementationt
{
protected:
  explicit single_value_index_ranget(const exprt &val);

public:
  const exprt &current() const override;
  bool advance_to_next() override;

protected:
  const exprt value;

private:
  bool available;
};

index_range_implementation_ptrt make_empty_index_range();
index_range_implementation_ptrt make_indeterminate_index_range();

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

  index_ranget index_range(const namespacet &ns) const
  {
    return index_ranget(index_range_implementation(ns));
  }

protected:
  virtual index_range_implementation_ptrt
  index_range_implementation(const namespacet &ns) const = 0;
};

#endif