/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

/// \file
/// The base of all structure abstractions

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_STRUCT_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_STRUCT_ABSTRACT_OBJECT_H

#include <analyses/variable-sensitivity/abstract_object.h>
#include <stack>

class abstract_environmentt;
class member_exprt;

class struct_abstract_objectt : public abstract_objectt
{
public:
  /// \param type: the type the abstract_object is representing
  explicit struct_abstract_objectt(const typet &type);

  /// \param type: the type the abstract_object is representing
  /// \param top: is the abstract_object starting as top
  /// \param bottom: is the abstract_object starting as bottom
  ///
  /// \return Start the abstract object at either top or bottom or neither
  ///         Asserts if both top and bottom are true
  struct_abstract_objectt(const typet &type, bool top, bool bottom);

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

  /// \param expr: the expression to use as the starting pointer for
  /// an abstract object
  /// \param environment: the environment in which the pointer is being
  ///                     created
  /// \param ns: the current namespace
  explicit struct_abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

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

  /// A helper function to evaluate the abstract object contained
  /// within a struct. More precise abstractions may override this
  /// to return more precise results.
  ///
  /// \param environment: the abstract environment
  /// \param member_expr: the expression uses to access a specific component
  /// \param ns: the current namespace
  ///
  /// \return The abstract object representing the value of that component. For
  ///         this abstraction this will always be top since we are not tracking
  ///         the struct.
  ///
  virtual abstract_object_pointert read_component(
    const abstract_environmentt &environment,
    const member_exprt &member_expr,
    const namespacet &ns) const;

  /// A helper function to evaluate writing to a component of a struct.
  /// More precise abstractions may override this to
  /// update what they are storing for a specific component.
  ///
  /// \param environment: the abstract environment
  /// \param ns: the current namespace
  /// \param stack: the remaining stack of expressions on the LHS to evaluate
  /// \param member_expr: the expression uses to access a specific component
  /// \param value: the value we are trying to write to the component
  /// \param merging_write: whether to over-write or to merge with the
  ///                       current value.  In other words is there
  ///                       any certainty that this write will happen.
  ///
  /// \return The struct_abstract_objectt representing the result of writing
  ///         to a specific component. In this case this will always be top
  ///         as we are not tracking the value of this struct.
  virtual abstract_object_pointert write_component(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const member_exprt &member_expr,
    const abstract_object_pointert &value,
    bool merging_write) const;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_STRUCT_ABSTRACT_OBJECT_H
