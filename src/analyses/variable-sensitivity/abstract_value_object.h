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

class constant_interval_exprt;

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

class value_range_implementationt;

using value_range_implementation_ptrt =
  std::unique_ptr<value_range_implementationt>;

class value_range_implementationt
{
public:
  virtual ~value_range_implementationt() = default;

  virtual value_range_implementation_ptrt reset() const = 0;

  virtual const abstract_object_pointert &current() const = 0;
  virtual bool advance_to_next() = 0;
};

class value_range_iteratort
{
public:
  const abstract_object_pointert &operator*() const
  {
    return range->current();
  }
  void operator++()
  {
    active = range->advance_to_next();
  }
  bool operator==(const value_range_iteratort &other) const
  {
    if(!active && !other.active)
      return true;
    return false;
  }
  bool operator!=(const value_range_iteratort &other) const
  {
    return !operator==(other);
  }

  value_range_iteratort(value_range_iteratort &&rhs)
    : range(std::move(rhs.range)), active(rhs.active)
  {
  }
  value_range_iteratort(const value_range_iteratort &) = delete;
  ~value_range_iteratort() = default;

private:
  value_range_iteratort() : range(nullptr), active(false)
  {
  }
  explicit value_range_iteratort(value_range_implementation_ptrt &&r)
    : range(std::move(r)), active(true)
  {
    active = range->advance_to_next();
  }

  value_range_implementation_ptrt range;
  bool active;

  friend class value_ranget;
};

class value_ranget
{
public:
  using value_type = abstract_object_pointert;

  explicit value_ranget(value_range_implementation_ptrt r) : range(r.release())
  {
  }
  value_ranget(value_ranget &&rhs) : range(rhs.range.release())
  {
  }
  value_ranget(const value_ranget &) = delete;
  ~value_ranget() = default;

  value_range_iteratort begin() const
  {
    return value_range_iteratort{range->reset()};
  }
  value_range_iteratort end() const
  {
    return {};
  }

private:
  value_range_implementation_ptrt range;
};

value_range_implementation_ptrt
make_single_value_range(const abstract_object_pointert &value);

class empty_value_ranget : public value_range_implementationt
{
public:
  const abstract_object_pointert &current() const override
  {
    return nothing;
  }
  bool advance_to_next() override
  {
    return false;
  }
  value_range_implementation_ptrt reset() const override
  {
    return util_make_unique<empty_value_ranget>();
  }

private:
  abstract_object_pointert nothing{0};
};

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

  value_ranget value_range() const
  {
    return value_ranget(value_range_implementation());
  }

  virtual constant_interval_exprt to_interval() const = 0;

  /// Interface for transforms
  ///
  /// \param expr: the expression to evaluate and find the result of it.
  ///              This will be the symbol referred to be op0()
  /// \param operands: an abstract_object (pointer) that represent
  ///                  the possible values of each operand
  /// \param environment: the abstract environment in which the
  ///                     expression is being evaluated
  /// \param ns: the current variable namespace
  ///
  /// \return Returns the abstract_object representing the result of
  ///         this expression to the maximum precision available.
  abstract_object_pointert expression_transform(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const final;

  virtual sharing_ptrt<const abstract_value_objectt>
  constrain(const exprt &lower, const exprt &upper) const = 0;

  abstract_object_pointert write(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const exprt &specifier,
    const abstract_object_pointert &value,
    bool merging_write) const final;

protected:
  using abstract_value_pointert = sharing_ptrt<const abstract_value_objectt>;

  /// Attempts to do a value/value merge if both are constants,
  /// otherwise falls back to the parent merge
  ///
  /// \param other: the abstract object to merge with
  /// \param widen_mode: Indicates if this is a widening merge
  ///
  /// \return Returns the result of the merge
  abstract_object_pointert merge(
    const abstract_object_pointert &other,
    const widen_modet &widen_mode) const final;

  abstract_object_pointert
  meet(const abstract_object_pointert &other) const final;

  virtual abstract_object_pointert merge_with_value(
    const abstract_value_pointert &other,
    const widen_modet &widen_mode) const = 0;

  virtual abstract_object_pointert
  meet_with_value(const abstract_value_pointert &other) const = 0;

  virtual index_range_implementation_ptrt
  index_range_implementation(const namespacet &ns) const = 0;

  virtual value_range_implementation_ptrt
  value_range_implementation() const = 0;

  sharing_ptrt<const abstract_value_objectt>
  as_value(const abstract_object_pointert &obj) const;
};

using abstract_value_pointert = sharing_ptrt<const abstract_value_objectt>;

#endif
