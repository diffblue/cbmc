/*******************************************************************\

 Module: Variable Sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

/// \file
/// An abstraction of an array value

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_FULL_ARRAY_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_FULL_ARRAY_ABSTRACT_OBJECT_H

#include <iosfwd>

#include <analyses/variable-sensitivity/abstract_aggregate_object.h>

class ai_baset;

class full_array_abstract_objectt : public abstract_aggregate_objectt<
                                      full_array_abstract_objectt,
                                      array_aggregate_typet>
{
public:
  typedef sharing_ptrt<full_array_abstract_objectt> const full_array_pointert;
  typedef abstract_aggregate_objectt<
    full_array_abstract_objectt,
    array_aggregate_typet>
    abstract_aggregate_baset;

  /// \param type: the type the abstract_object is representing
  explicit full_array_abstract_objectt(typet type);

  /// Start the abstract object at either top or bottom or neither
  /// Asserts if both top and bottom are true
  ///
  /// \param type: the type the abstract_object is representing
  /// \param top: is the abstract_object starting as top
  /// \param bottom: is the abstract_object starting as bottom
  full_array_abstract_objectt(typet type, bool top, bool bottom);

  /// \param expr: the expression to use as the starting pointer for
  ///              an abstract object
  /// \param environment: the environment the abstract object is
  ///                     being created in
  /// \param ns: the namespace
  full_array_abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

  /// the current known value about this object. For this array we
  /// print: { [0] - <output of object at index 0... }
  ///
  /// \param out: the stream to write to
  /// \param ai: the abstract interpreter that contains the abstract domain
  ///            (that contains the object ... )
  /// \param ns: the current namespace
  void output(std::ostream &out, const ai_baset &ai, const namespacet &ns)
    const override;

  /**
   * Update the location context for an abstract object.
   *
   * \param location the location to be updated
   *
   * \return a clone of this abstract object with its location context
   * updated
   */
  abstract_object_pointert
  write_location_context(const locationt &location) const override;
  abstract_object_pointert
  merge_location_context(const locationt &location) const override;

  /**
   * Apply a visitor operation to all sub elements of this abstract_object.
   * A sub element might be a member of a struct, or an element of an array,
   * for instance, but this is entirely determined by the particular
   * derived instance of abstract_objectt.
   *
   * \param visitor an instance of a visitor class that will be applied to
   * all sub elements
   * \return A new abstract_object if it's contents is modifed, or this if
   * no modification is needed
   */
  abstract_object_pointert
  visit_sub_elements(const abstract_object_visitort &visitor) const override;

protected:
  CLONE

  /// A helper function to read elements from an array. This will return
  /// the abstract object stored for that index, or top if we don't know
  /// about the specified index.
  /// If we can't resolve the index to a constant, we return top
  ///
  /// \param env: the environment
  /// \param expr: the expression used to access the specific value
  ///               in the array
  /// \param ns: the namespace
  ///
  /// \return An abstract object representing the value in the array
  abstract_object_pointert read_component(
    const abstract_environmentt &env,
    const exprt &expr,
    const namespacet &ns) const override;

  /// A helper function to evaluate writing to a index of an array.
  ///
  /// \param environment: the abstract environment
  /// \param ns: the namespace
  /// \param stack: the remaining stack of expressions on the LHS to evaluate
  /// \param expr: the expression uses to access a specific index
  /// \param value: the value we are trying to assign to that value in the array
  /// \param merging_write: Should this and all future writes be merged with the
  ///                       current value
  /// \return The abstract_object_pointert representing the result of writing
  ///         to a specific index.
  abstract_object_pointert write_component(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const exprt &expr,
    const abstract_object_pointert &value,
    bool merging_write) const override;

  void statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns) const override;

  /// Tries to do an array/array merge if merging with a constant array
  /// If it can't, falls back to parent merge
  ///
  /// \param other: The object to merge in
  /// \param widen_mode: Indicates if this is a widening merge
  ///
  /// \return Returns the result of the merge.
  abstract_object_pointert merge(
    const abstract_object_pointert &other,
    const widen_modet &widen_mode) const override;

  /// To validate that the struct object is in a valid state.
  /// This means either it is top or bottom, or if neither of those
  /// then there exists something in the map of components.
  /// If there is something in the map, then it can't be top or bottom
  ///
  /// \return Returns true if the struct is valid
  bool verify() const override;

  /// \brief Perform any additional structural modifications when setting this
  /// object to TOP
  void set_top_internal() override;

private:
  abstract_object_pointert read_element(
    const abstract_environmentt &env,
    const exprt &expr,
    const namespacet &ns) const;

  abstract_object_pointert write_element(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const exprt &expr,
    const abstract_object_pointert &value,
    bool merging_write) const;

  abstract_object_pointert write_sub_element(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const exprt &expr,
    const abstract_object_pointert &value,
    bool merging_write) const;

  abstract_object_pointert write_leaf_element(
    abstract_environmentt &environment,
    const namespacet &ns,
    const exprt &expr,
    const abstract_object_pointert &value,
    bool merging_write) const;

  // Since we don't store for any index where the value is top
  // we don't use a regular array but instead a map of array indices
  // to the value at that index
  struct mp_integer_hasht
  {
    size_t operator()(const mp_integer &i) const
    {
      return std::hash<BigInt::ullong_t>{}(i.to_ulong());
    }
  };

  typedef sharing_mapt<
    mp_integer,
    abstract_object_pointert,
    false,
    mp_integer_hasht>
    shared_array_mapt;

  shared_array_mapt map;

  void map_put(
    mp_integer index,
    const abstract_object_pointert &value,
    bool overrun);
  abstract_object_pointert map_find_or_top(
    mp_integer index,
    const abstract_environmentt &env,
    const namespacet &ns) const;

  /// Short hand method for creating a top element of the array
  ///
  /// \param env: the abstract environment
  /// \param ns: the namespace
  ///
  /// \return An abstract object pointer of type type().subtype() (i.e. the
  ///         type of the array's values).
  ///
  abstract_object_pointert
  get_top_entry(const abstract_environmentt &env, const namespacet &ns) const;

  /// Merges an array into this array
  ///
  /// \param other: The object to merge in
  /// \param widen_mode: Indicates if this is a widening merge
  ///
  /// \return Returns a new abstract object that is the result of the merge
  ///         unless the merge is the same as this abstract object, in which
  ///         case it returns this..
  abstract_object_pointert full_array_merge(
    const full_array_pointert &other,
    const widen_modet &widen_mode) const;

  exprt to_predicate_internal(const exprt &name) const override;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_FULL_ARRAY_ABSTRACT_OBJECT_H
