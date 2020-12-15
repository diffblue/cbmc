/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

/// \file
/// The base type of all abstract array representations

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ARRAY_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ARRAY_ABSTRACT_OBJECT_H

#include <analyses/variable-sensitivity/abstract_object.h>
#include <stack>

class abstract_environmentt;
class index_exprt;

class array_abstract_objectt : public abstract_objectt
{
public:
  /// \param type: the type the abstract_object is representing
  explicit array_abstract_objectt(const typet &type);

  /// Start the abstract object at either top or bottom or neither
  /// Asserts if both top and bottom are true
  ///
  /// \param type: the type the abstract_object is representing
  /// \param top: is the abstract_object starting as top
  /// \param bottom: is the abstract_object starting as bottom
  array_abstract_objectt(const typet &type, bool top, bool bottom);

  /// \param expr: the expression to use as the starting pointer for
  ///              an abstract object
  /// \param environment: the environment the abstract object is
  ///                     being created in
  /// \param ns: the namespace
  explicit array_abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

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
  ///
  /// To try and resolve different expressions with the maximum level
  /// of precision available.
  abstract_object_pointert expression_transform(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const override;

  /**
   * A helper function to evaluate writing to a component of an
   * abstract object. More precise abstractions may override this to
   * update what they are storing for a specific component.
   *
   * \param environment the abstract environment
   * \param ns the current namespace
   * \param stack the remaining stack of expressions on the LHS to evaluate
   * \param specifier the expression uses to access a specific component
   * \param value the value we are trying to write to the component
   * \param merging_write if true, this and all future writes will be merged
   * with the current value
   *
   * \return the abstract_objectt representing the result of writing
   * to a specific component.
   */
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

protected:
  CLONE

  /// A helper function to read elements from an array. More precise
  /// abstractions may override this to provide more precise results.
  ///
  /// \param env: the environment
  /// \param index: the expression used to access the specific value
  ///               in the array
  /// \param ns: the current variable namespace
  ///
  /// \return An abstract object representing the value in the array
  virtual abstract_object_pointert read_index(
    const abstract_environmentt &env,
    const index_exprt &index,
    const namespacet &ns) const;

  /// A helper function to evaluate writing to a component of a struct.
  /// More precise abstractions may override this to
  /// update what they are storing for a specific component.
  ///
  /// \param environment: the abstract environment
  /// \param ns: the namespace
  /// \param stack: the remaining stack of expressions on the LHS to evaluate
  /// \param index_expr: the expression uses to access a specific index
  /// \param value: the value we are trying to assign to that value in the array
  /// \param merging_write: ?
  ///
  /// \return The abstract_object_pointert representing the result of writing
  ///          to a specific component. In this case this will always be top
  ///          as we are not tracking the value in the array.
  virtual abstract_object_pointert write_index(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const index_exprt &index_expr,
    const abstract_object_pointert &value,
    bool merging_write) const;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ARRAY_ABSTRACT_OBJECT_H
