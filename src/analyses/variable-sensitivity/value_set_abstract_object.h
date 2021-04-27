/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: diffblue

\*******************************************************************/

/// \file
/// Value Set Abstract Object

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ABSTRACT_OBJECT_H

#include <analyses/variable-sensitivity/abstract_object_set.h>
#include <analyses/variable-sensitivity/abstract_value_object.h>

class value_set_abstract_objectt : public abstract_value_objectt,
                                   public value_set_tag
{
public:
  /// \copydoc abstract_objectt::abstract_objectt(const typet&)
  explicit value_set_abstract_objectt(const typet &type);

  /// \copydoc abstract_objectt::abstract_objectt(const typet &, bool, bool)
  value_set_abstract_objectt(const typet &type, bool top, bool bottom);

  value_set_abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

  static abstract_object_pointert
  make_value_set(const abstract_object_sett &initial_values);

  index_range_implementation_ptrt
  index_range_implementation(const namespacet &ns) const override;

  value_range_implementation_ptrt value_range_implementation() const override;

  /// \copydoc abstract_objectt::to_constant
  exprt to_constant() const override;
  constant_interval_exprt to_interval() const override;

  abstract_value_pointert
  constrain(const exprt &lower, const exprt &upper) const override;

  /// Getter for the set of stored abstract objects.
  /// \return the values represented by this abstract object
  const abstract_object_sett &get_values() const override
  {
    return values;
  }

  /// The threshold size for value-sets: past this threshold the object is
  /// either converted to interval or marked as `top`.
  static const size_t max_value_set_size = 10;

  void output(std::ostream &out, const ai_baset &ai, const namespacet &ns)
    const override;

protected:
  CLONE

  abstract_object_pointert merge_with_value(
    const abstract_value_pointert &other,
    const widen_modet &widen_mode) const override;

  abstract_object_pointert
  meet_with_value(const abstract_value_pointert &other) const override;

private:
  /// Setter for updating the stored values
  /// \param other_values: the new (non-empty) set of values
  void set_values(const abstract_object_sett &other_values);

  /// Update the set of stored values to \p new_values. Build a new abstract
  ///   object of the right type if necessary.
  /// \param new_values: potentially new set of values
  /// \return the abstract object representing \p new_values (either 'this' or
  ///   something new)
  abstract_object_pointert
  resolve_values(const abstract_object_sett &new_values) const;

  // data
  abstract_object_sett values;

  void set_top_internal() override;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ABSTRACT_OBJECT_H
