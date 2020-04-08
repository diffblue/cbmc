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


struct expr_pretty_hasht {
  std::size_t operator()(const exprt &expr) const {
    return std::hash<std::string>{}(expr.pretty());
  }
};

class value_set_abstract_objectt : public abstract_valuet
{
public:
  using value_sett = std::unordered_set<exprt, expr_pretty_hasht>;

  /// \copydoc abstract_objectt::abstract_objectt(const typet&)
  explicit value_set_abstract_objectt(const typet &type);

  value_set_abstract_objectt(const typet &type, value_sett values);

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
    return values.size() == 1 ? *values.begin() : nil_exprt{};
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
  const value_sett &get_values() const
  {
    return values;
  }

  /// The threshold size for value-sets: past this threshold the object is
  /// either converted to interval or marked as `top`.
  static constexpr size_t max_value_set_size = 10;

  void output(std::ostream &out, const ai_baset &ai, const namespacet &ns)
    const override;

protected:
  CLONE

  /// \copydoc abstract_object::merge
  abstract_object_pointert merge(abstract_object_pointert other) const override;

private:
  value_sett values;

  /// Recursively construct a combination \p sub_con from \p super_con and once
  ///   constructed call \p f.
  /// \param super_con: vector of some containers storing the values
  /// \param sub_con: the one combination being currently constructed
  /// \param f: callable with side-effects
  template <typename Con, typename F>
  void apply_function_to_cartesian_product(
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
        apply_function_to_cartesian_product(super_con, sub_con, f);
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
    apply_function_to_cartesian_product(super_con, sub_con, f);
  }

  /// Helper for converting context objects into its abstract-value children
  /// \p maybe_wrapped: either an abstract value (or a set of those) or one
  ///   wrapped in a context
  /// \return an abstract value without context (though it might be as set)
  static abstract_object_pointert
  maybe_unwrap_context(const abstract_object_pointert &maybe_wrapped);
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_ABSTRACT_OBJECT_H
