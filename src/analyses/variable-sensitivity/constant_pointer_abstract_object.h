/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

/// \file
/// An abstraction of a pointer that tracks a single pointer
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_POINTER_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_POINTER_ABSTRACT_OBJECT_H

#include <iosfwd>

#include <analyses/variable-sensitivity/abstract_pointer_object.h>
#include <analyses/variable-sensitivity/write_stack.h>

class constant_pointer_abstract_objectt : public abstract_pointer_objectt
{
private:
  typedef sharing_ptrt<constant_pointer_abstract_objectt>
    constant_pointer_abstract_pointert;

public:
  /// \param type: the type the abstract_object is representing
  explicit constant_pointer_abstract_objectt(const typet &type);

  /// \param type: the type the abstract_object is representing
  /// \param top: is the abstract_object starting as top
  /// \param bottom: is the abstract_object starting as bottom
  ///
  /// Start the abstract object at either top or bottom or neither
  /// Asserts if both top and bottom are true
  constant_pointer_abstract_objectt(const typet &type, bool top, bool bottom);

  constant_pointer_abstract_objectt(
    const typet &type,
    const constant_pointer_abstract_objectt &old);

  /// \param expr: the expression to use as the starting pointer for
  ///              an abstract object
  /// \param environment: the environment in which we evaluate expr
  /// \param ns: the current namespace
  constant_pointer_abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

  /// To try and find a constant expression for this abstract object
  ///
  /// \return Returns an expression representing the value if it can.
  ///          Returns a nil expression if it can be more than one value.
  ///          Returns null_pointer expression if it must be null
  ///          Returns an address_of_exprt with the value set to the
  ///          result of to_constant called on whatever abstract object this
  ///          pointer is pointing to.
  ///
  exprt to_constant() const override;

  /// Print the value of the pointer. Either NULL if nullpointer or
  /// ptr -> ( output of what the pointer is pointing to).
  ///
  /// \param out: the stream to write to
  /// \param ai: the domain in which this object appears
  ///            given as ai_baset so that the interface is the same
  ///            across all domains
  /// \param ns: the current namespace
  void output(std::ostream &out, const ai_baset &ai, const namespacet &ns)
    const override;

  /// A helper function to dereference a value from a pointer. Providing
  /// the pointer can only be pointing at one thing, returns an abstract
  /// object representing that thing. If null or top will return top.
  ///
  /// \param env: the environment
  /// \param ns: the namespace
  ///
  /// \return An abstract object representing the value this pointer is pointing
  ///         to
  abstract_object_pointert read_dereference(
    const abstract_environmentt &env,
    const namespacet &ns) const override;

  /// A helper function to evaluate writing to a pointers value.
  /// If the pointer can only be pointing to one element that it overwrites
  /// that element (or merges if merging_write) with the new value.
  /// If don't know what we are pointing to, we delegate to the parent.
  ///
  /// \param environment: the environment
  /// \param ns: the namespace
  /// \param stack: the remaining stack
  /// \param value: the value to write to the dereferenced pointer
  /// \param merging_write: is it a merging write (i.e. we aren't certain
  ///                       we are writing to this particular pointer therefore
  ///                       the value should be merged with whatever is already
  ///                       there or we are certain we are writing to this
  ///                       pointer so therefore the value can be replaced
  ///
  /// \return A modified abstract object representing this pointer after it
  ///         has been written to.
  abstract_object_pointert write_dereference(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const abstract_object_pointert &value,
    bool merging_write) const override;

  abstract_object_pointert typecast(
    const typet &new_type,
    const abstract_environmentt &environment,
    const namespacet &ns) const override;

  abstract_object_pointert ptr_diff(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const override;

  exprt ptr_comparison_expr(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const override;

  void get_statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns) const override;

protected:
  /// Set this abstract object to be the result of merging this
  /// abstract object. This calls the merge_constant_pointers if
  /// we are trying to merge a constant pointer we use the constant pointer
  /// constant pointer merge
  ///
  /// \param op1: the pointer being merged
  /// \param widen_mode: Indicates if this is a widening merge
  ///
  /// \return Returns the result of the merge.
  abstract_object_pointert merge(
    const abstract_object_pointert &op1,
    const widen_modet &widen_mode) const override;

  CLONE

private:
  bool same_target(abstract_object_pointert other) const;
  exprt offset() const;
  exprt offset_from(abstract_object_pointert other) const;

  /// Merges two constant pointers. If they are pointing at the same
  /// value, we merge, otherwise we set to top.
  ///
  /// \param other: the pointer being merged
  /// \param widen_mode: Indicates if this is a widening merge
  ///
  /// \return Returns a new abstract object that is the result of the merge
  ///         unless the merge is the same as this abstract object, in which
  ///         case it returns this.
  abstract_object_pointert merge_constant_pointers(
    const constant_pointer_abstract_pointert &other,
    const widen_modet &widen_mode) const;

  write_stackt value_stack;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_POINTER_ABSTRACT_OBJECT_H // NOLINT(*)
