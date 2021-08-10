/*******************************************************************\

Module: Struct abstract object

Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

/// \file
/// An abstraction of a structure that stores one abstract object per field
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_FULL_STRUCT_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_FULL_STRUCT_ABSTRACT_OBJECT_H

#include <analyses/variable-sensitivity/abstract_aggregate_object.h>
#include <iosfwd>
#include <util/sharing_map.h>

class full_struct_abstract_objectt : public abstract_aggregate_objectt<
                                       full_struct_abstract_objectt,
                                       struct_aggregate_typet>
{
public:
  typedef sharing_ptrt<full_struct_abstract_objectt> constant_struct_pointert;
  typedef abstract_aggregate_objectt<
    full_struct_abstract_objectt,
    struct_aggregate_typet>
    abstract_aggregate_baset;

  /**
   * \brief Explicit copy-constructor to make it clear that the shared_map
   *        used to store the values of fields is copy-constructed as well
   *        to ensure it shares as much data as possible.
   */
  full_struct_abstract_objectt(const full_struct_abstract_objectt &ao);

  /// \param type: the type the abstract_object is representing
  explicit full_struct_abstract_objectt(const typet &type);

  /// Start the abstract object at either top or bottom or
  /// neither asserts if both top and bottom are true
  ///
  /// \param type: the type the abstract_object is representing
  /// \param top: is the abstract_object starting as top
  /// \param bottom: is the abstract_object starting as bottom
  full_struct_abstract_objectt(const typet &type, bool top, bool bottom);

  /// \param expr: the expression to use as the starting pointer for an
  ///              abstract object
  /// \param environment: the environment in which we evaluate expr
  /// \param ns: the current namespace
  full_struct_abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

  /// To provide a human readable string to the out representing
  /// the current known value about this object. For this array we
  /// print: { .component_name=<output of object for component_name... }
  ///
  /// \param out: the stream to write to
  /// \param ai: the abstract interpreter that contains the abstract domain
  ///            (that contains the object ... )
  /// \param ns: the current namespace
  void output(
    std::ostream &out,
    const class ai_baset &ai,
    const class namespacet &ns) const override;

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

  void statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns) const override;

private:
  // no entry means component is top
  typedef sharing_mapt<irep_idt, abstract_object_pointert, false, irep_id_hash>
    shared_struct_mapt;
  shared_struct_mapt map;

  /// Performs an element wise merge of the map for each struct
  ///
  /// \param other: the other object being merged
  /// \param widen_mode: Indicates if this is a widening merge
  ///
  /// \return Returns a new abstract object that is the result of the merge
  ///         unless the merge is the same as this abstract object, in which
  ///         case it returns this.
  abstract_object_pointert merge_constant_structs(
    constant_struct_pointert other,
    const widen_modet &widen_mode) const;

protected:
  CLONE

  /// A helper function to evaluate the abstract object contained
  /// within a struct. More precise abstractions may override
  /// this to return more precise results.
  ///
  /// \param environment: the abstract environment
  /// \param expr: the expression uses to access a specific component
  /// \param ns: the current namespace
  ///
  /// \return The abstract object representing the value of that
  ///         component. For this abstraction this will always be top
  ///         since we are not tracking the struct.
  abstract_object_pointert read_component(
    const abstract_environmentt &environment,
    const exprt &expr,
    const namespacet &ns) const override;

  /// A helper function to evaluate writing to a component of a
  /// struct. More precise abstractions may override this to
  /// update what they are storing for a specific component.
  ///
  /// \param environment: the abstract environment
  /// \param ns: the current namespace
  /// \param stack: the remaining stack of expressions on the LHS to evaluate
  /// \param expr: the expression uses to access a specific component
  /// \param value: the value we are trying to write to the component
  /// \param merging_write: whether to over-write or to merge with the
  ///                       current value.  In other words is there
  ///                       any certainty that this write will happen.
  ///
  /// \return The struct_abstract_objectt representing the result of
  ///         writing to a specific component. In this case this will
  ///         always be top as we are not tracking the value of this
  ///          struct.
  abstract_object_pointert write_component(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const exprt &expr,
    const abstract_object_pointert &value,
    bool merging_write) const override;

  /// Function: full_struct_abstract_objectt::verify
  ///
  /// \return Returns true if the struct is valid
  ///
  /// To validate that the struct object is in a valid state.
  /// This means either it is top or bottom, or if neither of those
  /// then there exists something in the map of components.
  /// If there is something in the map, then it can't be top or bottom
  bool verify() const override;

  /// To merge an abstract object into this abstract object. If
  /// the other is also a struct, we perform a constant_structs merge
  /// Otherwise we call back to the parent merge.
  ///
  /// \param other: the other object being merged
  /// \param widen_mode: Indicates if this is a widening merge
  ///
  /// \return  Returns the result of the merge.
  abstract_object_pointert merge(
    const abstract_object_pointert &other,
    const widen_modet &widen_mode) const override;

  exprt to_predicate_internal(const exprt &name) const override;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_FULL_STRUCT_ABSTRACT_OBJECT_H
