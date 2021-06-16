/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

/// \file
/// an unordered set of value objects

#ifndef CBMC_ABSTRACT_OBJECT_SET_H
#define CBMC_ABSTRACT_OBJECT_SET_H

#include <analyses/variable-sensitivity/abstract_value_object.h>
#include <unordered_set>

class abstract_object_sett
{
public:
  using value_sett = std::unordered_set<
    abstract_object_pointert,
    abstract_hashert,
    abstract_equalert>;
  using const_iterator = value_sett::const_iterator;
  using value_type = value_sett::value_type;
  using size_type = value_sett::size_type;

  void insert(const abstract_object_pointert &o)
  {
    values.insert(o);
  }
  void insert(abstract_object_pointert &&o)
  {
    values.insert(std::move(o));
  }
  void insert(const abstract_object_sett &rhs)
  {
    values.insert(rhs.begin(), rhs.end());
  }
  void insert(const value_ranget &rhs)
  {
    for(auto const &value : rhs)
      insert(value);
  }

  void push_back(const abstract_object_pointert &v)
  {
    // alias for insert so we can use back_inserter
    values.insert(v);
  }

  abstract_object_pointert first() const
  {
    return *begin();
  }

  const_iterator begin() const
  {
    return values.begin();
  }
  const_iterator end() const
  {
    return values.end();
  }

  value_sett::size_type size() const
  {
    return values.size();
  }
  bool empty() const
  {
    return values.empty();
  }

  bool operator==(const abstract_object_sett &rhs) const
  {
    return values == rhs.values;
  }

  void clear()
  {
    values.clear();
  }

  void
  output(std::ostream &out, const ai_baset &ai, const namespacet &ns) const;

  /// Calculate the set of values as an interval.
  /// \return the constant_interval_exprt bounding the values
  constant_interval_exprt to_interval() const;

private:
  value_sett values;
};

class value_set_tag
{
public:
  virtual const abstract_object_sett &get_values() const = 0;
};

#endif //CBMC_ABSTRACT_OBJECT_SET_H
