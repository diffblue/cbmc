/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: diffblue

\*******************************************************************/

/// \file
/// Value Set Abstract Object

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ABSTRACT_OBJECT_H

#include <unordered_set>

#include <analyses/variable-sensitivity/abstract_value.h>

class value_set_abstract_objectt : public abstract_valuet
{
public:
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
  void set_values(const abstract_object_sett &other_values)
  {
    PRECONDITION(!other_values.empty());
    my_type = get_type(*other_values.begin());
    values = other_values;
    verify();
  }

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

  /// \copydoc abstract_objectt::read
  ///
  /// Delegate reading to stored values.
  abstract_object_pointert read(
    const abstract_environmentt &env,
    const exprt &specifier,
    const namespacet &ns) const override;

  /// \copydoc abstract_objectt::write
  ///
  /// Delegate writing to stored values.
  abstract_object_pointert write(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> stack,
    const exprt &specifier,
    const abstract_object_pointert value,
    bool merging_write) const override;

  /// Enforce casting to interval.
  /// \return the stored values abstracted to an interval
  abstract_object_pointert get_as_interval() const
  {
    return to_interval(values);
  }

  void output(std::ostream &out, const ai_baset &ai, const namespacet &ns)
    const override;

protected:
  CLONE

  /// Update the set of stored values to \p new_values. Build a new abstract
  ///   object of the right type if necessary.
  /// \param new_values: potentially new set of values
  /// \return the abstract object representing \p new_values (either 'this' or
  ///   something new)
  abstract_object_pointert
  resolve_new_values(const abstract_object_sett &new_values) const;

  /// \copydoc abstract_object::merge
  abstract_object_pointert merge(abstract_object_pointert other) const override;

private:
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

  /// Recursively construct a combination \p sub_con from \p super_con and once
  ///   constructed call \p f.
  /// \param super_con: vector of some containers storing the values
  /// \param sub_con: the one combination being currently constructed
  /// \param f: callable with side-effects
  template <typename Con, typename F>
  void apply_comb(
    const std::vector<Con> &super_con,
    std::vector<typename Con::value_type> &sub_con,
    F f) const
  {
    size_t n = sub_con.size();
    if(n == super_con.size())
      f(sub_con);
    else
    {
      for(const auto &value : super_con[n])
      {
        sub_con.push_back(value);
        apply_comb(super_con, sub_con, f);
        sub_con.pop_back();
      }
    }
  }

  /// Call the function \p f on every combination of elements in \p super_con.
  ///   Hence the arity of \p f is `super_con.size()`. <{1,2},{1},{1,2,3}> ->
  ///   f(1,1,1), f(1,1,2), f(1,1,3), f(2,1,1), f(2,1,2), f(2,1,3).
  /// \param super_con: vector of some containers storing the values
  /// \param f: callable with side-effects
  template <typename Con, typename F>
  void for_each_comb(const std::vector<Con> &super_con, F f) const
  {
    std::vector<typename Con::value_type> sub_con;
    apply_comb(super_con, sub_con, f);
  }

  /// Determine abstract-type of an abstract object \p other.
  /// \param other: the abstract object to get the type of
  /// \return the abstract-type of \p other
  static abstract_typet get_type(const abstract_object_pointert &other);

  /// Determine abstract-type of an expression-type \p type.
  /// \param type: the expression type to get the abstract-type of
  /// \return the abstract-type of \p type
  static abstract_typet type_to_abstract_type(const typet &type)
  {
    if(type.id() == ID_pointer)
    {
      return abstract_typet::POINTER;
    }
    else if(
      type.id() == ID_signedbv || type.id() == ID_unsignedbv ||
      type.id() == ID_fixedbv || type.id() == ID_c_bool ||
      type.id() == ID_bool || type.id() == ID_integer ||
      type.id() == ID_c_bit_field || type.id() == ID_floatbv)
    {
      return abstract_typet::CONSTANT;
    }
    else
    {
      return abstract_typet::UNSUPPORTED;
    }
  }

  /// Helper for converting singleton value sets into its only value.
  /// \p maybe_singleton: either a set of abstract values or a single value
  /// \return an abstract value without context
  static abstract_object_pointert
  maybe_extract_single_value(const abstract_object_pointert &maybe_singleton);

  /// Helper for converting context objects into its abstract-value children
  /// \p maybe_wrapped: either an abstract value (or a set of those) or one
  ///   wrapped in a context
  /// \return an abstract value without context (though it might be as set)
  static abstract_object_pointert
  maybe_unwrap_context(const abstract_object_pointert &maybe_wrapped);
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ABSTRACT_OBJECT_H
