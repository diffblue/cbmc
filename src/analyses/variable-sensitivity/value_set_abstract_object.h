/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: diffblue

\*******************************************************************/

/// \file
/// Value Set Abstract Object

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ABSTRACT_OBJECT_H

#include <unordered_set>

#include <analyses/variable-sensitivity/abstract_value_object.h>

class value_set_abstract_objectt : public abstract_value_objectt
{
public:
  using value_set_abstract_object_ptrt =
    std::shared_ptr<value_set_abstract_objectt>;

  using abstract_object_sett = std::unordered_set<
    abstract_object_pointert,
    abstract_hashert,
    abstract_equalert>;

  /// \copydoc abstract_objectt::abstract_objectt(const typet&)
  explicit value_set_abstract_objectt(const typet &type);

  /// \copydoc abstract_objectt::abstract_objectt(const typet &, bool, bool)
  value_set_abstract_objectt(const typet &type, bool top, bool bottom);

  value_set_abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

  index_range_ptrt index_range(const namespacet &ns) const override;

  /// \copydoc abstract_objectt::to_constant
  exprt to_constant() const override
  {
    verify();
    return values.size() == 1 ? (*values.begin())->to_constant()
                              : abstract_objectt::to_constant();
  }

  /// \copydoc abstract_objectt::expression_transform
  ///
  /// Transforms the \p expr for every combination of \p operands (since these
  /// can be value-sets as well).
  abstract_object_pointert expression_transform(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const override;

  /// Getter for the set of stored abstract objects.
  /// \return the values represented by this abstract object
  const abstract_object_sett &get_values() const
  {
    return values;
  }

  /// Setter for updating the stored values
  /// \param other_values: the new (non-empty) set of values
  void set_values(const abstract_object_sett &other_values);

  /// Distinguish the type of abstract objects stored in this value-set.
  enum class abstract_typet
  {
    CONSTANT,
    POINTER,
    UNSUPPORTED
  };

  /// Getter for the type of stored values
  /// \return the abstract-type stored here
  abstract_typet get_my_type() const
  {
    return my_type;
  }

  /// The threshold size for value-sets: past this threshold the object is
  /// either converted to interval or marked as `top`.
  static const size_t max_value_set_size = 10;

  /// \copydoc abstract_objectt::write
  ///
  /// Delegate writing to stored values.
  abstract_object_pointert write(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const exprt &specifier,
    const abstract_object_pointert &value,
    bool merging_write) const override;

  void output(std::ostream &out, const ai_baset &ai, const namespacet &ns)
    const override;

protected:
  CLONE

  /// \copydoc abstract_object::merge
  abstract_object_pointert merge(abstract_object_pointert other) const override;

private:
  abstract_object_pointert evaluate_conditional(
    const typet &type,
    const std::vector<abstract_object_sett> &operands,
    const abstract_environmentt &env,
    const namespacet &ns) const;

  /// Update the set of stored values to \p new_values. Build a new abstract
  ///   object of the right type if necessary.
  /// \param new_values: potentially new set of values
  /// \param environment: the abstract environment
  /// \return the abstract object representing \p new_values (either 'this' or
  ///   something new)
  abstract_object_pointert resolve_new_values(
    const abstract_object_sett &new_values,
    const abstract_environmentt &environment) const;

  /// Update the set of stored values to \p new_values. Build a new abstract
  ///   object of the right type if necessary.
  /// \param new_values: potentially new set of values
  /// \return the abstract object representing \p new_values (either 'this' or
  ///   something new)
  abstract_object_pointert
  resolve_values(const abstract_object_sett &new_values) const;

  // data
  abstract_typet my_type;
  abstract_object_sett values;

  /// Cast the set of values \p other_values to an interval.
  /// \param other_values: the value-set to be abstracted into an interval
  /// \return the interval-abstract-object containing \p other_values
  abstract_object_pointert
  to_interval(const abstract_object_sett &other_values) const;

  /// \copydoc abstract_objectt::verify
  bool verify() const override;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ABSTRACT_OBJECT_H
