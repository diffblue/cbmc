/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

/// \file
/// The base of all pointer abstractions
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_POINTER_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_POINTER_OBJECT_H

#include <analyses/variable-sensitivity/abstract_object.h>

class abstract_pointer_tag
{
};

class abstract_pointer_objectt : public abstract_objectt,
                                 public abstract_pointer_tag
{
public:
  /// \param type: the type the abstract_object is representing
  explicit abstract_pointer_objectt(const typet &type);

  /// Start the abstract object at either top or bottom or neither
  /// Asserts if both top and bottom are true
  ///
  /// \param type: the type the abstract_object is representing
  /// \param top: is the abstract_object starting as top
  /// \param bottom: is the abstract_object starting as bottom
  abstract_pointer_objectt(const typet &type, bool top, bool bottom);

  /// \param expr: the expression to use as the starting pointer for
  ///              an abstract object
  /// \param environment: the environment in which the pointer is being
  ///                     created
  /// \param ns: the current namespace
  explicit abstract_pointer_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

  abstract_object_pointert expression_transform(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const override;

  abstract_object_pointert write(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const exprt &specifier,
    const abstract_object_pointert &value,
    bool merging_write) const override;

  void get_statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns) const override;

  /// A helper function to read elements from an array. More precise
  /// abstractions may override this to provide more precise results.
  ///
  /// \param env: the environment
  /// \param ns: the namespace
  ///
  /// \return An abstract object representing the value being pointed to
  virtual abstract_object_pointert read_dereference(
    const abstract_environmentt &env,
    const namespacet &ns) const = 0;

  /// Evaluate writing to a pointer's value. More precise abstractions
  /// may override this provide more precise results.
  ///
  /// \param environment: the abstract environment
  /// \param ns: the namespace
  /// \param stack: the remaining stack of expressions on the LHS to evaluate
  /// \param value: the value we are trying to assign to what the pointer is
  ///               pointing to
  /// \param merging_write: is it a merging write (i.e. we aren't certain
  ///                       we are writing to this particular pointer therefore
  ///                       the value should be merged with whatever is already
  ///                       there or we are certain we are writing to this
  ///                       pointer so therefore the value can be replaced
  ///
  /// \return A modified abstract object representing this pointer after it
  ///         has been written to.
  virtual abstract_object_pointert write_dereference(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const abstract_object_pointert &value,
    bool merging_write) const = 0;

  virtual abstract_object_pointert typecast(
    const typet &new_type,
    const abstract_environmentt &environment,
    const namespacet &ns) const = 0;

  virtual abstract_object_pointert ptr_diff(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const = 0;

  virtual exprt ptr_comparison_expr(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const = 0;

private:
  abstract_object_pointert typecast_from_void_ptr(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const;
  abstract_object_pointert eval_ptr_diff(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const;
  abstract_object_pointert eval_ptr_comparison(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_POINTER_OBJECT_H
